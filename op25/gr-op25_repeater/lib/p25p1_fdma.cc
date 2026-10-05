/* -*- c++ -*- */
/* GROK version
 * Copyright 2010, 2011, 2012, 2013, 2014 Max H. Parke KA1RBI 
 * Copyright 2017-2025 Graham J. Norbury
 * 
 * This is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3, or (at your option)
 * any later version.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this software; see the file COPYING.  If not, write to
 * the Free Software Foundation, Inc., 51 Franklin Street,
 * Boston, MA 02110-1301, USA.
 */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include "p25p1_fdma.h"

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <errno.h>
#include <vector>
#include <array>
#include <algorithm>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <unistd.h>
#include "bch.h"
#include "op25_msg_types.h"
#include "op25_imbe_frame.h"
#include "p25_frame.h"
#include "p25_framer.h"
#include "rs.h"
#include <map>


namespace gr {
    namespace op25_repeater {



        /* Was 2.0s. Bumped to give longer RF fades / repeater-turnaround
         * gaps between confirmed-data bursts a chance to still be treated
         * as one continuous session rather than getting flushed and
         * re-started cold. Trade-off: a longer window also means two
         * genuinely separate bursts to the same RID are more likely to
         * get concatenated as if continuous -- watch REASM output for
         * structurally-wrong packets (bad IP version nibble, nonsense
         * ports) as the sign this has gone too far. */
        static const double REASM_WINDOW_SEC = 4.0;

        /* RidReasm is now declared in p25p1_fdma.h and lives as a member
         * (p25p1_fdma::reasm) instead of a file-scope global -- see the
         * comment on its declaration there. The free functions below
         * that used to touch a shared `g_reasm` directly now take the
         * caller's own RidReasm& instance explicitly. */

        static void reasm_reset(RidReasm& r)
        {
            r.rid = 0;
            r.last_ts = 0;
            r.last_ser = -1;
            r.buf.clear();
        }

        /* Classic hexdump -C style: offset, 16 hex bytes (gapped at 8),
         * ASCII alongside. Replaces the old single unbroken hex/ascii
         * line, which was also silently truncated at 64 bytes -- for a
         * 256-byte TMS message that meant most of it never printed
         * even in the "assembled" view, only scattered across the raw
         * per-block CONFIRMED lines. This covers the full length. */
        static void hexdump(const uint8_t* p, int n, const char* ts,
                            int msgq_id, uint32_t rid)
        {
            for (int off = 0; off < n; off += 16) {
                fprintf(stderr, "%s [%d] HEX rid=%u %04x: ", ts, msgq_id, rid, off);
                for (int i = 0; i < 16; i++) {
                    if (off + i < n)
                        fprintf(stderr, "%02x ", p[off + i]);
                    else
                        fprintf(stderr, "   ");
                    if (i == 7)
                        fputc(' ', stderr);
                }
                fprintf(stderr, " |");
                for (int i = 0; i < 16 && off + i < n; i++) {
                    uint8_t c = p[off + i];
                    fputc((c >= 32 && c < 127) ? c : '.', stderr);
                }
                fprintf(stderr, "|\n");
            }
        }

        /* Same local-integration pattern as tsbk_export (below), different
         * key/port so a consumer can tell the streams apart: real,
         * populated TMS text as JSON over UDP to 127.0.0.1:51003. Only
         * called for genuine content (same gate as the "*** TMS
         * PAYLOAD ***" alert) -- the routine empty 4-byte poll and the
         * beacon never reach this, so this stays a high-signal feed
         * rather than getting flooded with placeholder traffic. */
        static void tms_export(const char* ts, uint32_t rid, int port, const char* text, bool partial = false)
        {
            int fd = socket(AF_INET, SOCK_DGRAM, 0);
            if (fd < 0) return;
            struct sockaddr_in a;
            memset(&a, 0, sizeof(a));
            a.sin_family = AF_INET;
            a.sin_port = htons(51003);
            inet_aton("127.0.0.1", &a.sin_addr);
            char buf[600];
            int n = snprintf(buf, sizeof(buf),
                "{\"ts\":\"%s\",\"rid\":%u,\"port\":%d,\"partial\":%s,\"tms_text\":\"",
                ts, rid, port, partial ? "true" : "false");
            for (const char* p = text; *p && n < (int)sizeof(buf) - 4; p++) {
                if (*p == '"' || *p == '\\')
                    buf[n++] = '\\';
                buf[n++] = *p;
            }
            n += snprintf(buf + n, sizeof(buf) - n, "\"}");
            sendto(fd, buf, n, 0, (struct sockaddr*)&a, sizeof(a));
            close(fd);
        }

        /* Shared by reasm_print_ip() and the implausible-iplen salvage
         * path in reasm_dump(): try UTF-16LE first (low byte, then a
         * 0x00 high byte) -- matches full free-text messages -- and
         * fall back to a plain single-byte ASCII scan only when that
         * comes back completely empty (matches short canned/status
         * messages with no null padding, e.g. "HOURS"). Always null-
         * terminates text_buf and returns the char count written;
         * *ascii_fallback reports which path was used. */
        static int extract_tms_text(const uint8_t* buf, int len, char* text_buf,
                                     size_t text_buf_size, bool* ascii_fallback)
        {
            *ascii_fallback = false;
            int tlen = 0;
            for (int i = 0; i + 1 < len; i += 2) {
                if (buf[i+1] == 0 && buf[i] >= 32 && buf[i] < 127) {
                    if ((size_t)tlen < text_buf_size - 1)
                        text_buf[tlen++] = (char)buf[i];
                }
            }
            /* Always scan plain ASCII too. Choose it when UTF-16LE found
             * nothing, OR when it found far fewer chars than the ASCII
             * scan (a plain-ASCII message can contain one accidental
             * "xx 00" pair at an even offset -- e.g. a trailing NUL
             * after a ':' -- that made the UTF-16 pass return 1 char and
             * block the fallback). For genuine UTF-16LE text the two
             * counts are nearly equal (the 0x00 bytes are skipped by the
             * ASCII scan), so those messages stay on the UTF-16 path.
             * A lone stray printable byte in an otherwise-binary buffer
             * is noise, so still require a real run (MIN_ASCII_FALLBACK_LEN). */
            {
                static const int MIN_ASCII_FALLBACK_LEN = 4;
                char ascii_buf[600];
                int ascii_tlen = 0;
                for (int i = 0; i < len; i++) {
                    if (buf[i] >= 32 && buf[i] < 127) {
                        if ((size_t)ascii_tlen < sizeof(ascii_buf) - 1 &&
                            (size_t)ascii_tlen < text_buf_size - 1)
                            ascii_buf[ascii_tlen++] = (char)buf[i];
                    }
                }
                if (ascii_tlen >= MIN_ASCII_FALLBACK_LEN &&
                    (tlen == 0 || ascii_tlen > 2 * tlen + 4)) {
                    memcpy(text_buf, ascii_buf, ascii_tlen);
                    tlen = ascii_tlen;
                    *ascii_fallback = true;
                }
            }
            text_buf[tlen] = '\0';
            return tlen;
        }

        /* Best-effort partial decode -- fires when reassembly is
         * provably incomplete (REASM wait) but there's already a
         * valid IP+UDP header and some real payload bytes sitting in
         * the buffer. REASM/TMS_TEXT proper only ever print once a
         * datagram is 100% complete (tot==have); that's correct for
         * the "is this exact number of bytes right" checks, but it
         * means a message that's genuinely 13 of 16 blocks in --
         * readable, useful, just missing its tail to a real Viterbi
         * failure on the last couple blocks -- was previously
         * invisible anywhere except the raw CONFIRMED blk hex. This
         * prints (and exports) whatever text IS there so far, clearly
         * labeled partial, and naturally gets called again with more
         * text each time a new burst adds to a still-incomplete
         * session -- a live, growing preview rather than all-or-
         * nothing. Deliberately a separate function from
         * reasm_print_ip rather than retrofitting it with a partial
         * mode, so the already-working complete-datagram path is
         * never at risk of being disturbed by this. */
        static void reasm_print_ip_partial(int msgq_id, const char* ts,
                                           const uint8_t* p, int avail,
                                           int declared_iplen, uint32_t rid)
        {
            if (avail < 20)
                return;
            uint8_t ihl = (p[0] & 0x0f) * 4;
            if (avail < ihl + 8)
                return;
            uint8_t proto = p[9];
            if (proto != 17)
                return;

            const uint8_t* u = p + ihl;
            uint16_t dport = (u[2]<<8)|u[3];
            int pay = avail - ihl - 8;
            if (pay <= 4)
                return;   /* nothing beyond the routine fixed-size replies yet */

            char text_buf[600];
            bool ascii_fb = false;
            int tlen = extract_tms_text(u + 8, pay, text_buf, sizeof(text_buf), &ascii_fb);
            if (tlen < 4)
                return;   /* not enough decoded so far to be worth printing */

            fprintf(stderr,
                    "%s [%d] *** TMS_TEXT_PARTIAL rid=%u have=%d/%d text=%s ***\n",
                    ts, msgq_id, rid, avail, declared_iplen, text_buf);

            /* 64414 is OTAR/KMM key-management traffic, never text. */
            if (dport != 64414)
                tms_export(ts, rid, dport, text_buf, true);   /* partial=true */
        }

        static void reasm_print_ip(int msgq_id, const char* ts,
                                   const uint8_t* p, int iplen, uint32_t rid,
                                   bool salvage = false)
        {
            /* salvage=true means this datagram was recovered from a burst
             * whose 12-byte header failed CRC -- rid may be an unverified
             * guess (or 0), and the blocks that built this buffer were
             * accepted on Viterbi cost + shape alone, not a session we
             * were already tracking. Tag every line so this never reads
             * as an ordinary, fully-verified decode, and never hand it to
             * tms_export() -- that's for verified content only. */
            const char* tag = salvage ? "SALVAGE_" : "";
            if (iplen < 20)
                return;

            uint8_t ihl = (p[0] & 0x0f) * 4;
            uint16_t tot = (p[2] << 8) | p[3];
            uint8_t proto = p[9];
            uint32_t src = (p[12]<<24)|(p[13]<<16)|(p[14]<<8)|p[15];
            uint32_t dst = (p[16]<<24)|(p[17]<<16)|(p[18]<<8)|p[19];

            fprintf(stderr,
                    "%s [%d] %sIP rid=%u ver=%u ihl=%u tot=%u have=%d proto=0x%02x "
                    "%u.%u.%u.%u -> %u.%u.%u.%u\n",
                    ts, msgq_id, tag, rid,
                    p[0] >> 4, ihl, tot, iplen, proto,
                    (src>>24)&0xff, (src>>16)&0xff, (src>>8)&0xff, src&0xff,
                    (dst>>24)&0xff, (dst>>16)&0xff, (dst>>8)&0xff, dst&0xff);

            if (tot > iplen)
                fprintf(stderr, "%s [%d] %sIP SHORT rid=%u need=%u have=%d missing=%d\n",
                        ts, msgq_id, tag, rid, tot, iplen, tot - iplen);

            if (proto != 17 || iplen < ihl + 8)
                return;

            const uint8_t* u = p + ihl;
            uint16_t sport = (u[0]<<8)|u[1];
            uint16_t dport = (u[2]<<8)|u[3];
            uint16_t ulen  = (u[4]<<8)|u[5];
            int pay = iplen - ihl - 8;
            if (pay < 0) pay = 0;

            fprintf(stderr,
                    "%s [%d] %sUDP rid=%u %u.%u.%u.%u:%u -> %u.%u.%u.%u:%u "
                    "udp_len=%u payload=%d\n",
                    ts, msgq_id, tag, rid,
                    (src>>24)&0xff, (src>>16)&0xff, (src>>8)&0xff, src&0xff, sport,
                    (dst>>24)&0xff, (dst>>16)&0xff, (dst>>8)&0xff, dst&0xff, dport,
                    ulen, pay);

            if (ulen > 8 && (ulen - 8) > pay)
                fprintf(stderr, "%s [%d] %sUDP SHORT rid=%u udp_payload=%u have=%d\n",
                        ts, msgq_id, tag, rid, ulen - 8, pay);

            /* Port 4007 is Motorola TMS (confirmed: gop25/sdrtrunk source,
             * Motorola LRRP/ARS/TMS case-study docs). Every TMS packet
             * we've ever captured on this system -- 79+ instances across
             * two full nights -- has been the identical 4-byte
             * "mailbox empty" reply. Anything bigger is a real, populated
             * text and worth a loud, greppable line of its own rather
             * than blending into routine UDP output. */
            if (dport == 4007 && pay > 4)
                fprintf(stderr,
                        "%s [%d] *** %sTMS PAYLOAD rid=%u len=%d (port 4007, normally 4) ***\n",
                        ts, msgq_id, tag, rid, pay);
            /* Mirror for port 4005 (ARS) -- always 3-byte fixed in
             * every capture so far, so this is precautionary rather
             * than fixing an observed miss. Costs nothing to cover it
             * in case AFRRCS content ever lands there too. */
            if (dport == 4005 && pay > 3)
                fprintf(stderr,
                        "%s [%d] *** %sARS PAYLOAD rid=%u len=%d (port 4005, normally 3) ***\n",
                        ts, msgq_id, tag, rid, pay);

            /* Port 64414 keepalive: always carries the sender's own RID
             * at a fixed offset in the payload (right after the "26 00
             * 08 00" trailer), confirmed across every fleet block seen
             * so far (411xxx and 401xxx alike) -- exact match every
             * time. That gives a free correctness check on every one of
             * these (they fire constantly), and it means this specific
             * byte shape is routine, self-identifying traffic, not a
             * framer leak -- worth remembering, since this exact
             * pattern (a plausible-looking RID trailing a block) was
             * the centerpiece of an earlier leak/ceiling debate. Skip
             * the full hexdump for this known-shape traffic; one
             * compact line is enough, and it stays out of the way of
             * anything actually worth reading by eye. */
            if (dport == 64414 && pay >= 21) {
                /* Beacon/keepalive shape -- routine self-identifying
                 * traffic, never a real message. In salvage mode this is
                 * exactly the "not worth the noise" case: no rid to
                 * cross-check it against anyway (that's the whole reason
                 * we're here), so skip the line entirely rather than
                 * print a MISMATCH that means nothing. */
                if (salvage)
                    return;
                uint32_t self_id = ((uint32_t)u[8+18] << 16) |
                                    ((uint32_t)u[8+19] << 8)  |
                                     (uint32_t)u[8+20];
                fprintf(stderr, "%s [%d] BEACON rid=%u self_id=%u %s\n",
                        ts, msgq_id, rid, self_id,
                        (self_id == rid) ? "ok" : "*** MISMATCH ***");
                return;
            }

            fprintf(stderr, "%s [%d] %sHEXDUMP rid=%u len=%d:\n", ts, msgq_id, tag, rid, pay);
            hexdump(u + 8, pay, ts, msgq_id, rid);

            /* Space-separated, fixed fields first so this is easy to
             * awk/parse downstream: timestamp, msgq, a stable tag, then
             * rid=, then the free-text message to end of line. Grep for
             * "TMS_TEXT" instead of the old "utf16:" label. Builds a
             * plain buffer alongside the printed version so it can also
             * go out over tms_export() for genuine content.
             *
             * Two different TMS payload encodings show up in practice.
             * Full free-text messages come across as UTF-16LE -- each
             * printable char followed by a 0x00 high byte -- and the
             * loop below decodes exactly that. But short canned/status
             * messages (observed: a plain "HOURS") come across as
             * ordinary single-byte ASCII with no null padding at all,
             * so every pair in that loop fails the high==0 test and the
             * message silently prints as empty even though the text is
             * sitting right there in the hexdump above. Rather than
             * guess which encoding a given payload uses, try UTF-16LE
             * first (unchanged behavior for every message that already
             * decodes correctly), and only fall back to a plain-ASCII
             * byte scan when that pass comes back completely empty. */
            char text_buf[600];
            bool ascii_fallback = false;
            int tms_tlen = extract_tms_text(u + 8, pay, text_buf, sizeof(text_buf), &ascii_fallback);
            fprintf(stderr, "%s [%d] %sTMS_TEXT rid=%u text=%s%s\n",
                    ts, msgq_id, tag, rid, text_buf,
                    ascii_fallback ? " (ascii fallback)" : "");

            /* Mirrors the ARS PAYLOAD gate above -- 4007 is the normal
             * TMS path, 4005 covered defensively in case content ever
             * lands there too. Salvage content never reaches tms_export()
             * -- that path is for content we actually trust (a verified
             * header, or a live session we were already tracking), and
             * rid may be an unverified guess or 0 here. */
            if (!salvage && ((dport == 4007 && pay > 4) || (dport == 4005 && pay > 3) ||
                             (dport != 4007 && dport != 4005 && dport != 64414 && tms_tlen >= 4)))
                tms_export(ts, rid, dport, text_buf);
        }

        static void reasm_dump(RidReasm& r, int msgq_id, const char* ts)
        {
            if (r.buf.empty())
                return;
            for (;;) {
                uint8_t* p = r.buf.data();
                size_t n = r.buf.size();
                int off = -1;
                for (size_t i = 0; i + 20 <= n; i++) {
                    if (p[i] == 0x45) { off = (int)i; break; }
                }
                if (off < 0) {
                    if (n >= 8)
                        fprintf(stderr, "%s [%d] REASM raw rid=%u leftover=%zu\n",
                                ts, msgq_id, r.rid, n);
                    break;
                }
                int tot = (p[off+2] << 8) | p[off+3];
                if (tot < 20)
                    break;

                /* Cross-check the IP header's declared total length (tot)
                 * against the UDP header's own length field (udp_len) --
                 * two independently-decoded fields that must agree if
                 * both decoded cleanly. A single bit error landing in
                 * just the 2 tot bytes was otherwise silently accepted
                 * as-is, and since same-RID retries within
                 * REASM_WINDOW_SEC get concatenated into one buffer, a
                 * too-large tot reads straight past the real end of this
                 * datagram and into the start of whatever's next --
                 * observed in the field as one message's real tail glued
                 * directly onto the next message's start (e.g.
                 * "...LOCHQEAHS_Messaging_..." -- a genuine ending
                 * immediately followed by the fixed prefix that starts
                 * every real message). When they disagree, prefer the
                 * udp_len-derived length: not guaranteed correct either,
                 * but it's the one Motorola's stack actually needs right
                 * to deliver the page at all, and the mismatch is now
                 * logged loudly (grep "LEN MISMATCH") so these are
                 * visible instead of silently corrupting output. */
                /* Real datagrams on this system have never exceeded ~200
                 * bytes (TMS/SNDCP text, BEACON keepalives, etc.). Blocks
                 * are fixed-size (16 payload bytes each) and any unused
                 * tail of an already-CONFIRMED block is padded with 0xF5
                 * filler -- visible throughout these logs as trailing
                 * "f5 f5 f5 ..." runs -- not zeroed and not flagged as
                 * "not yet real data". If the UDP length field (u[4],u[5])
                 * happens to land on that filler, 0xF5F5 decodes as
                 * udp_len=62965, giving derived=ihl+62965=62985 -- an
                 * exact, reproducible value (confirmed hitting this same
                 * 62985 on two independent receivers/RIDs). Uncapped, the
                 * "prefer derived length" logic below then latches onto
                 * that phantom 63KB datagram and holds the reassembly
                 * open (REASM wait / repeated HOLD REQUEST renewals) for
                 * minutes waiting for a message that was never coming,
                 * instead of the far shorter real one already in hand. */
                static const int MAX_PLAUSIBLE_IPLEN = 1500;
                int iplen = tot;
                uint8_t ihl = (p[off] & 0x0f) * 4;
                uint8_t proto = p[off+9];
                if (proto == 17 && (size_t)(off + ihl + 8) <= n) {
                    const uint8_t* u = p + off + ihl;
                    uint16_t udp_len = (u[4] << 8) | u[5];
                    int derived = ihl + udp_len;
                    if (udp_len >= 8 && derived != tot) {
                        if (derived <= MAX_PLAUSIBLE_IPLEN) {
                            fprintf(stderr,
                                    "%s [%d] REASM LEN MISMATCH rid=%u tot=%d ihl+udp_len=%d "
                                    "(ihl=%u udp_len=%u) -- using derived length\n",
                                    ts, msgq_id, r.rid, tot, derived, ihl, udp_len);
                            iplen = derived;
                        } else {
                            fprintf(stderr,
                                    "%s [%d] REASM LEN MISMATCH rid=%u tot=%d ihl+udp_len=%d "
                                    "(ihl=%u udp_len=%u) -- derived length implausible "
                                    "(likely unfilled 0xF5 padding), keeping tot=%d instead\n",
                                    ts, msgq_id, r.rid, tot, derived, ihl, udp_len, tot);
                        }
                    }
                }
                if (iplen > MAX_PLAUSIBLE_IPLEN) {
                    fprintf(stderr,
                            "%s [%d] REASM rid=%u implausible iplen=%d (>%d) -- treating as "
                            "corrupt header, discarding session instead of waiting\n",
                            ts, msgq_id, r.rid, iplen, MAX_PLAUSIBLE_IPLEN);

                    /* The LENGTH field lied here, not necessarily the bytes
                     * behind it -- confirmed twice in the field (rid=4116893
                     * and rid=4116896, both on the Radnor site, both a
                     * clean, legible address) where the accumulated buffer
                     * held a perfectly good message and this exact guard
                     * discarded it anyway because one glued-on length byte
                     * came out wrong. r.rid is still a verified RID here
                     * (this session's header passed CRC when it was
                     * opened) -- only the length math downstream of it is
                     * untrustworthy. So before giving up on the bytes, try
                     * a direct text scan on the raw buffer, skipping the
                     * IP/UDP length fields entirely rather than trusting
                     * them to find the payload -- same UTF-16LE/ASCII
                     * extraction used everywhere else in this file. */
                    bool have_udp = proto == 17 && (size_t)(off + ihl + 8) <= n;
                    const uint8_t* udp_payload = have_udp ? p + off + ihl + 8 : nullptr;
                    int udp_payload_avail = have_udp ? (int)(n - (off + ihl + 8)) : 0;

                    if (r.buf.size() >= 20) {
                        char text_buf[600];
                        bool ascii_fallback = false;
                        int tlen;

                        /* Prefer scanning from right after the IP+UDP
                         * header -- ihl/proto are reliable (separate
                         * bytes from the length field that lied), and
                         * this avoids the IP header's OWN leading bytes
                         * decoding as bogus text. Confirmed this matters:
                         * byte 0 of essentially every real IPv4 packet is
                         * 0x45 (version 4, ihl 5), and the very next byte
                         * (ToS) is almost always 0x00 -- paired together
                         * that's a spurious leading 'E' prepended to
                         * every single salvage if scanning from the raw
                         * buffer start instead. Only fall back to the raw
                         * buffer when there's no safe structured offset
                         * to start from at all. */
                        if (have_udp)
                            tlen = extract_tms_text(udp_payload, udp_payload_avail,
                                                     text_buf, sizeof(text_buf),
                                                     &ascii_fallback);
                        else
                            tlen = extract_tms_text(p, (int)n, text_buf, sizeof(text_buf),
                                                     &ascii_fallback);

                        if (tlen > 0) {
                            fprintf(stderr,
                                    "%s [%d] SALVAGE_TMS_TEXT rid=%u (iplen was implausible -- "
                                    "length field untrusted, scanned directly instead) "
                                    "text=%s%s\n",
                                    ts, msgq_id, r.rid, text_buf,
                                    ascii_fallback ? " (ascii fallback)" : "");

                            /* dport is two bytes entirely separate from
                             * the length field that actually lied here --
                             * safe to trust on its own. Export it the
                             * same way a normal decode would, so this
                             * doesn't just sit in the log file --
                             * partial=true since this bypassed the length
                             * math rather than confirming the datagram
                             * was byte-exact. */
                            if (have_udp) {
                                const uint8_t* u = p + off + ihl;
                                uint16_t dport = (u[2] << 8) | u[3];
                                if (dport == 4007 || dport == 4005 ||
                                    (dport != 64414 && tlen >= 4))
                                    tms_export(ts, r.rid, dport, text_buf, true);
                            }
                        }
                    }

                    r.buf.clear();
                    r.rid = 0;
                    r.last_ser = -1;
                    break;
                }
                if (iplen < 20)
                    break;
                if (off + iplen > (int)n) {
                    int have = (int)n - off;
                    fprintf(stderr,
                            "%s [%d] REASM wait rid=%u have=%d need=%d (more blocks expected)\n",
                            ts, msgq_id, r.rid, have, iplen);
                    reasm_print_ip_partial(msgq_id, ts, p + off, have, iplen, r.rid);
                    break;
                }

                fprintf(stderr, "%s [%d] REASM rid=%u len=%d\n",
                        ts, msgq_id, r.rid, iplen);
                reasm_print_ip(msgq_id, ts, p + off, iplen, r.rid);

                r.buf.erase(r.buf.begin(),
                            r.buf.begin() + off + iplen);
            }
            if (r.buf.size() < 20)
                r.buf.clear();
            if (r.buf.empty()) {
                r.rid = 0;
                r.last_ser = -1;
            }
        }

        static void reasm_flush(RidReasm& r, int msgq_id, const char* ts)
        {
            reasm_dump(r, msgq_id, ts);
            reasm_reset(r);
        }

        static void reasm_burst(RidReasm& r, int msgq_id, const char* ts, uint32_t rid,
                                double now, const uint8_t d34[][18], int n34)
        {
            if (n34 <= 0)
                return;

            bool same_session = (r.rid == rid) &&
                                 ((now - r.last_ts) < REASM_WINDOW_SEC);

            /* Reject only an exact duplicate of the last block already
             * accepted for this RID -- an air retry of the same block.
             * We have no verified example of what a legitimate
             * multi-burst serial jump looks like (the old exact-next_ser
             * check never once matched a real continuation in the field,
             * only routine self-contained pokes that never needed it),
             * so don't flush on anything else -- just append and let
             * reasm_dump's IP-length check decide if more is needed. */
            if (same_session && d34[0][0] == (uint8_t)r.last_ser) {
                fprintf(stderr, "%s [%d] REASM dup rid=%u ser=%u -- ignored (air retry)\n",
                        ts, msgq_id, rid, d34[0][0]);
                return;
            }

            if (!same_session && !r.buf.empty())
                reasm_flush(r, msgq_id, ts);   /* different RID, or session gone cold */

            r.rid = rid;
            r.last_ts = now;

            for (int i = 0; i < n34; i++) {
                r.buf.insert(r.buf.end(), d34[i] + 2, d34[i] + 18);
                r.last_ser = d34[i][0];
            }

            reasm_dump(r, msgq_id, ts);
        }

        /* Fire-and-forget TSBK export to a local integration point --
         * every TSBK that passes CRC, raw and unframed: byte 0 = opcode,
         * byte 1 = last-block flag, bytes 2-13 = the raw 12-byte TSBK.
         * 14 bytes total, no JSON, nothing to parse but fixed offsets.
         * NAC isn't included -- it's been a constant 0x368 for this
         * whole investigation, so add it back only if that ever stops
         * being true. Sent to 127.0.0.1:51002 -- a local-only feed for
         * whatever consumes it next. (This used to be described as
         * "separate from op25_hold_notify's 51001" -- that dead-end
         * trunked-dwell integration to a remote uniden-monitor host was
         * removed; this export is unrelated and unaffected.) */
        static void tsbk_export(const char* ts, int nac, uint8_t op,
                                uint8_t lb, const uint8_t* raw12)
        {
            (void)ts; (void)nac;   /* kept in the signature so call sites don't change */
            int fd = socket(AF_INET, SOCK_DGRAM, 0);
            if (fd < 0) return;
            struct sockaddr_in a;
            memset(&a, 0, sizeof(a));
            a.sin_family = AF_INET;
            a.sin_port = htons(51002);
            inet_aton("127.0.0.1", &a.sin_addr);
            uint8_t buf[14];
            buf[0] = op;
            buf[1] = lb;
            memcpy(buf + 2, raw12, 12);
            sendto(fd, buf, sizeof(buf), 0, (struct sockaddr*)&a, sizeof(a));
            close(fd);
        }

        static void dump_pdu_burst(const char* ts, uint32_t rid, uint32_t fr_len,
               const uint8_t* hdr12,
               const bit_vector& bv, int bl_len,
               const uint8_t blks[][18], int n34)
            {
                char fn[128];
                snprintf(fn, sizeof(fn), "/tmp/pdu_%u_%s.bin", rid, ts);
                (void)fn;   /* built but intentionally unused -- see below */
                /* sanitize ts if it has spaces */
                /* "wb" (truncate), not "ab" (append): this was appending
                 * forever with no rotation or cap, growing unbounded for
                 * as long as the process runs. The filename itself
                 * ("pdu_last.bin") implies the original intent was
                 * "most recent capture only" -- truncating on each write
                 * matches that and removes the disk-growth risk entirely. */
                FILE* f = fopen("/tmp/pdu_last.bin", "wb");
                if (!f) return;
                fprintf(f, "TS %s rid=%u fr_len=%u bl_len=%d n34=%d\n",
                        ts, rid, fr_len, bl_len, n34);
                fprintf(f, "HDR");
                for (int i = 0; i < 12; i++) fprintf(f, " %02x", hdr12[i]);
                fprintf(f, "\n");
                for (int b = 1; b < bl_len; b++) {
                    unsigned off = 48 + 64 + b * 196;
                    fprintf(f, "RAW%d ", b);
                    for (unsigned i = 0; i < 196 && off + i < bv.size(); i++)
                        fputc(bv[off + i] ? '1' : '0', f);
                    fprintf(f, "\n");
                    if (b <= n34) {
                        fprintf(f, "D34%d", b);
                        for (int i = 0; i < 18; i++) fprintf(f, " %02x", blks[b - 1][i]);
                        fprintf(f, "\n");
                    }
                }
                fputc('\n', f);
                fclose(f);
            }
        
        
        static const int64_t TIMEOUT_THRESHOLD = 1000000;

        p25p1_fdma::~p25p1_fdma()
        {
            delete framer;
        }

        static uint16_t crc16(uint8_t buf[], int len) {
            if (buf == 0)
                return -1;
            uint32_t poly = (1<<12) + (1<<5) + (1<<0);
            uint32_t crc = 0;
            for(int i=0; i<len; i++) {
                uint8_t bits = buf[i];
                for (int j=0; j<8; j++) {
                    uint8_t bit = (bits >> (7-j)) & 1;
                    crc = ((crc << 1) | bit) & 0x1ffff;
                    if (crc & 0x10000)
                        crc = (crc & 0xffff) ^ poly;
                }
            }
            crc = crc ^ 0xffff;
            return crc & 0xffff;
        }

        /* translated from p25craft.py Michael Ossmann <mike@ossmann.com>  */
        static uint32_t crc32(uint8_t buf[], int len) {	/* length is nr. of bits */
            uint32_t g = 0x04c11db7;
            uint64_t crc = 0;
            for (int i = 0; i < len; i++) {
                crc <<= 1;
                int b = ( buf [i / 8] >> (7 - (i % 8)) ) & 1;
                if (((crc >> 32) ^ b) & 1)
                    crc ^= g;
            }
            crc = (crc & 0xffffffff) ^ 0xffffffff;
            return crc;
        }

        /* find_min is from wireshark/plugins/p25/packet-p25cai.c */
        /* Copyright 2008, Michael Ossmann <mike@ossmann.com>  */
        /* return the index of the lowest value in a list */
        static int find_min(uint8_t list[], int len) {
            int min = list[0];	
            int index = 0;	
            int unique = 1;	
            int i;

            for (i = 1; i < len; i++) {
                if (list[i] < min) {
                    min = list[i];
                    index = i;
                    unique = 1;
                } else if (list[i] == min) {
                    unique = 0;
                }
            }
            /* return -1 if a minimum can't be found */
            if (!unique)
                return -1;

            return index;
        }

        /* count_bits is from wireshark/plugins/p25/packet-p25cai.c */
        /* Copyright 2008, Michael Ossmann <mike@ossmann.com>  */
        /* count the number of 1 bits in an int */
        static int count_bits(unsigned int n) {
            int i = 0;
            for (i = 0; n != 0; i++)
                n &= n - 1;
            return i;
        }

        /* adapted from wireshark/plugins/p25/packet-p25cai.c */
        /* Copyright 2008, Michael Ossmann <mike@ossmann.com>  */
        /* deinterleave and trellis1_2 decoding */
        /* buf is assumed to be a buffer of 12 bytes */
        static int block_deinterleave(bit_vector& bv, unsigned int start, uint8_t* buf) {
            static const uint16_t deinterleave_tb[] = {
                0,  1,  2,  3,  52, 53, 54, 55, 100,101,102,103, 148,149,150,151,
                4,  5,  6,  7,  56, 57, 58, 59, 104,105,106,107, 152,153,154,155,
                8,  9, 10, 11,  60, 61, 62, 63, 108,109,110,111, 156,157,158,159,
                12, 13, 14, 15,  64, 65, 66, 67, 112,113,114,115, 160,161,162,163,
                16, 17, 18, 19,  68, 69, 70, 71, 116,117,118,119, 164,165,166,167,
                20, 21, 22, 23,  72, 73, 74, 75, 120,121,122,123, 168,169,170,171,
                24, 25, 26, 27,  76, 77, 78, 79, 124,125,126,127, 172,173,174,175,
                28, 29, 30, 31,  80, 81, 82, 83, 128,129,130,131, 176,177,178,179,
                32, 33, 34, 35,  84, 85, 86, 87, 132,133,134,135, 180,181,182,183,
                36, 37, 38, 39,  88, 89, 90, 91, 136,137,138,139, 184,185,186,187,
                40, 41, 42, 43,  92, 93, 94, 95, 140,141,142,143, 188,189,190,191,
                44, 45, 46, 47,  96, 97, 98, 99, 144,145,146,147, 192,193,194,195,
                48, 49, 50, 51 };

            uint8_t hd[4];
            int b, d, j;
            int state = 0;
            uint8_t codeword;

            static const uint8_t next_words[4][4] = {
                {0x2, 0xC, 0x1, 0xF},
                {0xE, 0x0, 0xD, 0x3},
                {0x9, 0x7, 0xA, 0x4},
                {0x5, 0xB, 0x6, 0x8}
            };

            memset(buf, 0, 12);

            for (b=0; b < 98*2; b += 4) {
                codeword = (bv[start+deinterleave_tb[b+0]] << 3) + 
                    (bv[start+deinterleave_tb[b+1]] << 2) + 
                    (bv[start+deinterleave_tb[b+2]] << 1) + 
                    bv[start+deinterleave_tb[b+3]]     ;

                /* try each codeword in a row of the state transition table */
                for (j = 0; j < 4; j++) {
                    /* find Hamming distance for candidate */
                    hd[j] = count_bits(codeword ^ next_words[state][j]);
                }
                /* find the dibit that matches the most codeword bits (minimum Hamming distance) */
                state = find_min(hd, 4);
                /* error if minimum can't be found */
                if(state == -1)
                    return -1;	// decode error, return failure
                /* It also might be nice to report a condition where the minimum is
                 * non-zero, i.e. an error has been corrected.  It probably shouldn't
                 * be a permanent failure, though.
                 *
                 * DISSECTOR_ASSERT(hd[state] == 0);
                 */

                /* append dibit onto output buffer */
                d = b >> 2;	// dibit ctr
                if (d < 48) {
                    buf[d >> 2] |= state << (6 - ((d%4) * 2));
                }
            }
            return 0;
        }


        /* Rate 3/4 confirmed data block: same 196-bit interleave as 1/2,
         * TIA Table 7-2 / kchmck p25.rs tribit FSM. Out = 18 octets
         * (2-byte serial/CRC + 16 data). Returns 0 on OK. 
         * russ.innes@gmail.com 2026 */
         
        static int block_deinterleave_34(bit_vector& bv, unsigned int start, uint8_t* buf18)
        {
            static const uint16_t deint[] = {
                 0,  1,  2,  3, 52, 53, 54, 55,100,101,102,103,148,149,150,151,
                 4,  5,  6,  7, 56, 57, 58, 59,104,105,106,107,152,153,154,155,
                 8,  9, 10, 11, 60, 61, 62, 63,108,109,110,111,156,157,158,159,
                12, 13, 14, 15, 64, 65, 66, 67,112,113,114,115,160,161,162,163,
                16, 17, 18, 19, 68, 69, 70, 71,116,117,118,119,164,165,166,167,
                20, 21, 22, 23, 72, 73, 74, 75,120,121,122,123,168,169,170,171,
                24, 25, 26, 27, 76, 77, 78, 79,124,125,126,127,172,173,174,175,
                28, 29, 30, 31, 80, 81, 82, 83,128,129,130,131,176,177,178,179,
                32, 33, 34, 35, 84, 85, 86, 87,132,133,134,135,180,181,182,183,
                36, 37, 38, 39, 88, 89, 90, 91,136,137,138,139,184,185,186,187,
                40, 41, 42, 43, 92, 93, 94, 95,140,141,142,143,188,189,190,191,
                44, 45, 46, 47, 96, 97, 98, 99,144,145,146,147,192,193,194,195
            };
            static const uint8_t pairs[16][2] = {
                {0,2},{2,2},{1,3},{3,3},{3,2},{1,2},{2,3},{0,3},
                {3,1},{1,1},{2,0},{0,0},{0,1},{2,1},{1,0},{3,0}
            };
            static const uint8_t stmap[8][8] = {
                {0,8,4,12,2,10,6,14},
                {4,12,2,10,6,14,0,8},
                {1,9,5,13,3,11,7,15},
                {5,13,3,11,7,15,1,9},
                {3,11,7,15,1,9,5,13},
                {7,15,1,9,5,13,3,11},
                {2,10,6,14,0,8,4,12},
                {6,14,0,8,4,12,2,10}
            };

            if (start + 195 >= bv.size())
                return -1;

            uint8_t coded[196];
            for (int i = 0; i < 196; i++)
                coded[i] = bv[start + deint[i]] ? 1 : 0;

            const int N = 49; /* 98 dibits / 2 = 49 steps */
            const int INF = 100000;
            int cost[50][8], prevs[50][8];
            for (int t = 0; t <= N; t++)
                for (int s = 0; s < 8; s++) {
                    cost[t][s] = INF;
                    prevs[t][s] = -1;
                }
            cost[0][0] = 0;

            for (int t = 0; t < N; t++) {
                int obs = (coded[4*t] << 3) | (coded[4*t+1] << 2) |
                          (coded[4*t+2] << 1) |  coded[4*t+3];
                for (int s = 0; s < 8; s++) {
                    if (cost[t][s] >= INF)
                        continue;
                    for (int nx = 0; nx < 8; nx++) {
                        int p = stmap[s][nx];
                        int exp = (pairs[p][0] << 2) | pairs[p][1];
                        int ham = 0, x = obs ^ exp;
                        while (x) { ham += x & 1; x >>= 1; }
                        int nc = cost[t][s] + ham;
                        if (nc < cost[t+1][nx]) {
                            cost[t+1][nx] = nc;
                            prevs[t+1][nx] = s;
                        }
                    }
                }
            }

            int end = 0;
            for (int s = 1; s < 8; s++)
                if (cost[N][s] < cost[N][end])
                    end = s;

            int path[49];
            int s = end;
            for (int t = N; t > 0; t--) {
                path[t-1] = s;
                s = prevs[t][s];
                if (s < 0)
                    return -1;
            }

            /* pack 49 tribits -> 18 bytes (last nibble unused) */
            memset(buf18, 0, 18);
            unsigned acc = 0, nbits = 0, o = 0;
            for (int i = 0; i < N && o < 18; i++) {
                acc = (acc << 3) | (path[i] & 7);
                nbits += 3;
                while (nbits >= 8 && o < 18) {
                    nbits -= 8;
                    buf18[o++] = (uint8_t)((acc >> nbits) & 0xff);
                    acc &= (1u << nbits) - 1;
                }
            }
            /* Instrumentation only -- threshold/behavior unchanged. Logs
             * the Viterbi path cost so failed (and near-threshold
             * successful) blocks can be checked for whether real data is
             * clustering just above the cost>8 cutoff -- that's the
             * signal to actually justify raising the threshold, versus
             * failures being spread out (meaning the threshold isn't
             * the bottleneck and loosening it would just admit noise). */
            int c = cost[N][end];
            if (c > 8) {
                fprintf(stderr, "  D34 cost=%d FAIL (threshold=8)\n", c);
                return -1;
            }
            if (c > 0)
                fprintf(stderr, "  D34 cost=%d ok\n", c);
            return 0;
        }

        void p25p1_fdma::set_debug(int debug)
        {
            d_debug = debug;
            crypt_algs.set_debug(debug);
            framer->set_debug(debug);
        }

        void p25p1_fdma::set_nac(int nac)
        {
            d_nac = nac;
            framer->set_nac(nac);
            if (d_debug >= 10)
                fprintf(stderr, "%s p25p1_fdma::set_nac: 0x%03x\n", logts.get(d_msgq_id), d_nac);
        }

        void p25p1_fdma::set_dwell_rid(uint32_t rid)
        {
            /* UNUSED as of 2026-09-26: multi_rx.py's fixed-frequency
             * channels no longer retune, and the Uniden CC monitor that
             * used to call this (to arm the salvage-gate's now-removed
             * reasm.rid == d_dwell_rid check, see process_blocks()) has
             * been dropped rather than kept solely for that. Left in
             * place, harmless, in case per-RID dwell tracking is
             * reintroduced later -- nothing currently calls it, so
             * d_dwell_rid stays 0 and this body never runs.
             *
             * Original rationale, kept for that future reintroduction:
             * reasm holds this instance's reassembly session -- whatever
             * it's holding belongs to the PREVIOUS dwell's RID on this
             * same channel. If we don't drop it here, a header-CRC
             * failure in the first REASM_WINDOW_SEC of the new dwell
             * hits the salvage branch in process_blocks() and attributes
             * real data blocks from the NEW RID to the stale cached
             * reasm.rid -- see the cross-RID misattribution this was
             * added to close (traced from the 09/25 log: nblk=5
             * header-CRC-fail bursts on RID 4116773's dwell decoding
             * identical bytes across unrelated captures). Clearing on
             * every dwell change makes that misattribution structurally
             * impossible rather than relying on timing to avoid it.
             * (reasm was previously a single process-wide global shared
             * across every channel -- now a per-instance member, so this
             * reset only ever affects this channel's own session.) */
            if (rid != d_dwell_rid && reasm.rid) {
                fprintf(stderr, "%s set_dwell_rid: %u -> %u, dropping stale reasm session for rid=%u\n",
                        logts.get(d_msgq_id), d_dwell_rid, rid, reasm.rid);
                reasm.rid = 0;
                reasm.last_ser = -1;
                reasm.buf.clear();
            }
            d_dwell_rid = rid;
            if (d_debug >= 10)
                fprintf(stderr, "%s p25p1_fdma::set_dwell_rid: %u\n", logts.get(d_msgq_id), d_dwell_rid);
        }

        void p25p1_fdma::crypt_behavior(int behavior)
        {
            d_behavior = behavior;
            framer->crypt_behavior(behavior);
        }

        p25p1_fdma::p25p1_fdma(op25_audio& udp, log_ts& logger, int debug, bool do_imbe, bool do_output, bool do_msgq, gr::msg_queue::sptr queue, std::deque<int16_t> &output_queue, bool do_audio_output, int msgq_id) :
            write_bufp(0),
            d_debug(debug),
            d_do_imbe(do_imbe),
            d_do_output(do_output),
            d_do_msgq(do_msgq),
            d_msgq_id(msgq_id),
            d_do_audio_output(do_audio_output),
            d_nac(0),
            d_behavior(0),
            d_msg_queue(queue),
            output_queue(output_queue),
            framer(new p25_framer(logger, debug, msgq_id)),
            qtimer(op25_timer(TIMEOUT_THRESHOLD)),
            op25audio(udp),
            logts(logger),
            crypt_algs(logger, debug, msgq_id),
            ess_keyid(0),
            ess_algid(0x80),
            vf_tgid(0)
        {
        }

        void p25p1_fdma::process_duid(uint32_t const duid, uint32_t const nac, const uint8_t* buf, const int len) {
            char wbuf[256];
            int p = 0;
            if (!d_do_msgq)
                return;
            assert (len+2 <= (int)sizeof(wbuf));
            wbuf[p++] = (nac >> 8) & 0xff;
            wbuf[p++] = nac & 0xff;
            if (buf) {
                memcpy(&wbuf[p], buf, len);	// copy data
                p += len;
            }
            send_msg(std::string(wbuf, p), duid);
            qtimer.reset();
        }

        void p25p1_fdma::process_HDU(const bit_vector& A) {
            if (d_debug >= 10) {
                fprintf (stderr, "%s NAC 0x%03x HDU:  ", logts.get(d_msgq_id), framer->nac);
            }

            uint32_t MFID;
            int i, j, k, ec;
            size_t errs = 0, gly_errs = 0;
            std::vector<uint8_t> HB(63,0); // hexbit vector
            k = 0;
            for (i = 0; i < 36; i ++) {
                uint32_t CW = 0;
                for (j = 0; j < 18; j++) {  // 18 bits / cw
                    CW = (CW << 1) + A [ hdu_codeword_bits[k++] ];
                }
                HB[27 + i] = gly24128Dec(CW, &errs) & 63;
                gly_errs += errs;
            }
            ec = rs16.decode(HB); // Reed Solomon (36,20,17) error correction

            if ((ec >= 0) && (ec <= 8)) { // upper limit of 8 corrections
                j = 27;												// 72 bit MI
                for (i = 0; i < 9;) {
                    ess_mi[i++] = (uint8_t)  (HB[j  ]         << 2) + (HB[j+1] >> 4);
                    ess_mi[i++] = (uint8_t) ((HB[j+1] & 0x0f) << 4) + (HB[j+2] >> 2);
                    ess_mi[i++] = (uint8_t) ((HB[j+2] & 0x03) << 6) +  HB[j+3];
                    j += 4;
                }
                MFID      =  (HB[j  ]         <<  2) + (HB[j+1] >> 4);						// 8 bit MfrId
                ess_algid = ((HB[j+1] & 0x0f) <<  4) + (HB[j+2] >> 2);						// 8 bit AlgId
                ess_keyid = ((HB[j+2] & 0x03) << 14) + (HB[j+3] << 8) + (HB[j+4] << 2) + (HB[j+5] >> 4);	// 16 bit KeyId
                vf_tgid   = ((HB[j+5] & 0x0f) << 12) + (HB[j+6] << 6) +  HB[j+7];				// 16 bit TGID

                if (d_debug >= 10) {
                    fprintf (stderr, "ESS: tgid=%d, mfid=%x, algid=%x, keyid=%x, mi=%02x %02x %02x %02x %02x %02x %02x %02x %02x",
                            vf_tgid, MFID, ess_algid, ess_keyid,
                            ess_mi[0], ess_mi[1], ess_mi[2], ess_mi[3], ess_mi[4], ess_mi[5],ess_mi[6], ess_mi[7], ess_mi[8]);
                }
            }

            if (d_debug >= 10) {
                fprintf (stderr, ", gly_errs=%lu, rs_errs=%d\n", gly_errs, ec);
            }
        }

        void p25p1_fdma::process_LLDU(const bit_vector& A, std::vector<uint8_t>& HB) {
            process_duid(framer->duid, framer->nac, NULL, 0);

            int i, j, k;
            k = 0;
            for (i = 0; i < 24; i ++) { // 24 10-bit codewords
                uint32_t CW = 0;
                for (j = 0; j < 10; j++) {  // 10 bits / cw
                    CW = (CW << 1) + A[ imbe_ldu_ls_data_bits[k++] ];
                }
                HB[39 + i] = hmg1063Dec( CW >> 4, CW & 0x0f );
            }
        }

        void p25p1_fdma::process_LDU1(const bit_vector& A) {
            if (d_debug >= 10) {
                fprintf (stderr, "%s NAC 0x%03x LDU1: ", logts.get(d_msgq_id), framer->nac);
            }

            std::vector<uint8_t> HB(63,0); // hexbit vector
            process_LLDU(A, HB);
            process_LCW(HB);

            if (d_debug >= 10) {
                fprintf (stderr, "\n");
            }

            process_voice(A, FT_LDU1);
        }

        void p25p1_fdma::process_LDU2(const bit_vector& A) {
            uint16_t next_keyid;
            uint8_t  next_algid;
            uint8_t  next_mi[9] = {0};
            bool next_ess_valid = false;

            if (d_debug >= 10) {
                fprintf (stderr, "%s NAC 0x%03x LDU2: ", logts.get(d_msgq_id), framer->nac);
            }

            std::vector<uint8_t> HB(63,0); // hexbit vector
            process_LLDU(A, HB);

            int i, j, ec;
            ec = rs8.decode(HB); // Reed Solomon (24,16,9) error correction
            if ((ec >= 0) && (ec <= 4)) {	// upper limit of 4 corrections
                j = 39;                                                             // 72 bit MI
                for (i = 0; i < 9;) {
                    next_mi[i++] = (uint8_t)  (HB[j  ]         << 2) + (HB[j+1] >> 4);
                    next_mi[i++] = (uint8_t) ((HB[j+1] & 0x0f) << 4) + (HB[j+2] >> 2);
                    next_mi[i++] = (uint8_t) ((HB[j+2] & 0x03) << 6) +  HB[j+3];
                    j += 4;
                }
                next_algid =  (HB[j  ]         <<  2) + (HB[j+1] >> 4);             //  8 bit AlgId
                next_keyid = ((HB[j+1] & 0x0f) << 12) + (HB[j+2] << 6) + HB[j+3];   // 16 bit KeyId
                next_ess_valid = true;

                if (d_debug >= 10) {
                    fprintf (stderr, "ESS: algid=%x, keyid=%x, mi=%02x %02x %02x %02x %02x %02x %02x %02x %02x, rs_errs=%d\n",
                            next_algid, next_keyid,
                            next_mi[0], next_mi[1], next_mi[2], next_mi[3], next_mi[4], next_mi[5], next_mi[6], next_mi[7], next_mi[8],
                            ec); 
                }
            }

            // When configured to skip encrypted audio (crypt_behavior >= 2) there is no key to
            // decrypt with, so apply a newly received encrypted AlgId before this LDU2's voice is
            // processed. Otherwise LDU2 is decoded under the previous (cleared) crypto state and
            // its 180 ms of vocoder output reaches the audio sink before the gate engages. Key-
            // loaded operation (crypt_behavior 0 and 1) keeps the original ordering so that the MI
            // and keystream sequencing used for decryption are unchanged.
            if ((d_behavior >= 2) && next_ess_valid && (next_algid != 0x80)) {
                ess_algid = next_algid;
            }

            process_voice(A, FT_LDU2);

            // replace existing ess with newly received data now that voice processing is complete
            // if new ess was not received correctly, compute the next ess_mi from the last one
            if (next_ess_valid) {
                ess_algid = next_algid;
                ess_keyid = next_keyid;
                memcpy(ess_mi, next_mi, sizeof(next_mi));
            } else {
                op25_crypt_algs::cycle_p25_mi(ess_mi);
            }

            std::string encr = "{\"encrypted\": " + std::to_string(encrypted() ? 1 : 0) + ", \"algid\": " + std::to_string(ess_algid) + ", \"keyid\": " + std::to_string(ess_keyid) + "}";
            send_msg(encr, M_P25_JSON_DATA);
        }

        void p25p1_fdma::process_TTDU() {
            process_duid(framer->duid, framer->nac, NULL, 0);
            reset_ess();

            if ((d_do_imbe || d_do_audio_output) && (framer->duid == 0x3 || framer->duid == 0xf)) {  // voice termination
                op25audio.send_audio_flag(op25_audio::DRAIN);
            }
        }

        void p25p1_fdma::process_TDU3() {
            if (d_debug >= 10) {
                fprintf (stderr, "%s NAC 0x%03x TDU3:  ", logts.get(d_msgq_id), framer->nac);
            }

            process_TTDU();

            if (d_debug >= 10) {
                fprintf (stderr, "\n");
            }
        }

        void p25p1_fdma::process_TDU15(const bit_vector& A) {
            if (d_debug >= 10) {
                fprintf (stderr, "%s NAC 0x%03x TDU15:  ", logts.get(d_msgq_id), framer->nac);
            }

            process_TTDU();

            int i, j, k;
            size_t gly_errs = 0, errs = 0;
            std::vector<uint8_t> HB(63,0); // hexbit vector
            k = 0;
            for (i = 0; i <= 22; i += 2) {
                uint32_t CW = 0;
                for (j = 0; j < 12; j++) {   // 12 24-bit codewords
                    CW = (CW << 1) + A [ hdu_codeword_bits[k++] ];
                    CW = (CW << 1) + A [ hdu_codeword_bits[k++] ];
                }
                uint32_t D = gly24128Dec(CW, &errs);
                HB[39 + i] = D >> 6;
                HB[40 + i] = D & 63;
            }
            process_LCW(HB);

            if (d_debug >= 10) {
                fprintf (stderr, ", gly_errs=%lu\n", gly_errs);
            }
        }

        void p25p1_fdma::process_LCW(std::vector<uint8_t>& HB) {
            int ec = rs12.decode(HB); // Reed Solomon (24,12,13) error correction
            if ((ec < 0) || (ec > 6)) // upper limit of 6 corrections
                return; // failed CRC

            int i, j;
            std::vector<uint8_t> lcw(9,0); // Convert hexbits to bytes
            j = 0;
            for (i = 0; i < 9;) {
                lcw[i++] = (uint8_t)  (HB[j+39]         << 2) + (HB[j+40] >> 4);
                lcw[i++] = (uint8_t) ((HB[j+40] & 0x0f) << 4) + (HB[j+41] >> 2);
                lcw[i++] = (uint8_t) ((HB[j+41] & 0x03) << 6) +  HB[j+42];
                j += 4;
            }

            std::string pdu(11,0);
            pdu[0] = (framer->nac >> 8) & 0xff; pdu[1] = framer->nac & 0xff;
            for (int i = 0; i < 9; i++) {
                pdu[2+i] = lcw[i];
            }
            send_msg(pdu, M_P25_FDMA_LCW);

            int pb =   (lcw[0] >> 7);
            int sf =  ((lcw[0] & 0x40) >> 6);
            int lco =   lcw[0] & 0x3f;
            std::string s = "";

            if (d_debug >= 10) {
                fprintf(stderr, "LCW: ec=%d, pb=%d, sf=%d, lco=%d : %02x %02x %02x %02x %02x %02x %02x %02x %02x",
                        ec, pb, sf, lco, lcw[0], lcw[1], lcw[2], lcw[3], lcw[4], lcw[5], lcw[6], lcw[7], lcw[8]);
            }
        }


    static void dump_p25_udp_payload(const std::vector<std::array<uint8_t, 18>>& confirmed_blocks, int msgq_id, double timestamp, uint32_t source_rid) 
    {
        // 1. Stitch rule: Extract bytes [2..17] from every data block
        std::vector<uint8_t> raw_stream;
        raw_stream.reserve(confirmed_blocks.size() * 16);
        for (size_t i = 0; i < confirmed_blocks.size(); i++) {
            raw_stream.insert(raw_stream.end(), confirmed_blocks[i].begin() + 2, confirmed_blocks[i].end());
        }

        // 2. Absolute baseline bounds check (2 bytes SNDCP + 20 bytes IP + 8 bytes UDP = 30 bytes)
        if (raw_stream.size() < 30) return;

        // Verify the packet is IPv4 (Index 2 holds the '45' signature)
        if ((raw_stream[2] >> 4) != 4) return;

        // Verify the transport layer is UDP (Protocol field is at Index 11)
        if (raw_stream[11] != 0x11) return;

        // 3. Extract IP Addresses from absolute indices [14..17] and [18..21]
        char src_ip[16];
        char dst_ip[16];
        sprintf(src_ip, "%d.%d.%d.%d", raw_stream[14], raw_stream[15], raw_stream[16], raw_stream[17]);
        sprintf(dst_ip, "%d.%d.%d.%d", raw_stream[18], raw_stream[19], raw_stream[20], raw_stream[21]);

        // 4. Extract UDP Sockets from absolute indices
        uint16_t src_port = (raw_stream[22] << 8) | raw_stream[23];
        uint16_t dst_port = (raw_stream[24] << 8) | raw_stream[25];
        uint16_t udp_len  = (raw_stream[26] << 8) | raw_stream[27];

        // 5. Explicit Payload Isolation (Jumps exactly past the 30 network header bytes)
        size_t payload_offset = 30;
        if (raw_stream.size() <= payload_offset) return;

        size_t payload_len = raw_stream.size() - payload_offset;
        if (udp_len > 8) {
            size_t true_udp_len = (size_t)(udp_len - 8);
            if (true_udp_len < payload_len) {
                payload_len = true_udp_len;
            }
        }

        if (payload_len == 0) return;

        // 6. Format Time Status Clock
        char time_str[32];
        time_t raw_time = (time_t)timestamp;
        int millis = (int)((timestamp - raw_time) * 1000);
        struct tm *time_info = localtime(&raw_time);
        if (time_info) {
            strftime(time_str, sizeof(time_str), "%m/%d/%y %H:%M:%S", time_info);
            sprintf(time_str + strlen(time_str), ".%03d", millis);
        } else {
            sprintf(time_str, "%.3f", timestamp);
        }

        // 7. Output clean, verified network telemetry row
        fprintf(stderr, "%s [%d] RID:%u | CAD UDP: %s:%u -> %s:%u (Bytes=%zu)\n", 
                time_str, msgq_id, source_rid, src_ip, src_port, dst_ip, dst_port, payload_len);

        // 8. Visual Data Grid View
        fprintf(stderr, "-----------------------------------------------------------------\n");
        for (size_t i = 0; i < payload_len; i += 16) {
            fprintf(stderr, "  %04zu: ", i);

            for (size_t j = 0; j < 16; j++) {
                if (i + j < payload_len) {
                    fprintf(stderr, "%02x ", raw_stream[payload_offset + i + j]);
                } else {
                    fprintf(stderr, "   ");
                }
            }
            fprintf(stderr, " | ");

            for (size_t j = 0; j < 16; j++) {
                if (i + j < payload_len) {
                    uint8_t ch = raw_stream[payload_offset + i + j];
                    if (ch >= 32 && ch < 127) {
                        fputc((int)ch, stderr);
                    } else {
                        fputc('.', stderr);
                    }
                }
            }
            fprintf(stderr, "\n");
        }
        fprintf(stderr, "-----------------------------------------------------------------\n");
    }

        struct pdu_reasm {
            uint32_t rid;
            double   last_ts;
            uint8_t  last_ser;
            std::vector<std::array<uint8_t, 18>> blocks;
        };

        
        static void dump_p25_udp_payload(const std::vector<std::array<uint8_t, 18>>& blocks,
                                         int msgq_id, const char* ts, uint32_t rid)
        {
            std::vector<uint8_t> buf;
            buf.reserve(blocks.size() * 16);
            for (size_t i = 0; i < blocks.size(); i++)
                buf.insert(buf.end(), blocks[i].begin() + 2, blocks[i].end());

            /* SNDCP SN-DATA is often 51 00; slide to IPv4 */
            size_t off = 0;
            while (off + 1 < buf.size() && buf[off] != 0x45)
                off++;
            if (off + 28 > buf.size())
                return;
            if ((buf[off] >> 4) != 4)
                return;
            if (buf[off + 9] != 0x11)
                return;

            uint16_t ip_len  = (buf[off+2] << 8) | buf[off+3];
            uint16_t src_prt = (buf[off+20] << 8) | buf[off+21];
            uint16_t dst_prt = (buf[off+22] << 8) | buf[off+23];
            uint16_t udp_len = (buf[off+24] << 8) | buf[off+25];
            size_t po = off + 28;
            size_t plen = (udp_len > 8) ? (size_t)(udp_len - 8) : 0;
            if (po + plen > buf.size())
                plen = buf.size() - po;

            fprintf(stderr,
                "%s [%d] RID:%u CAD-UDP %u.%u.%u.%u:%u -> %u.%u.%u.%u:%u ip=%u udp_pl=%zu\n",
                ts, msgq_id, rid,
                buf[off+12], buf[off+13], buf[off+14], buf[off+15], src_prt,
                buf[off+16], buf[off+17], buf[off+18], buf[off+19], dst_prt,
                ip_len, plen);

            for (size_t i = 0; i < plen; i += 16) {
                fprintf(stderr, "  %04zu: ", i);
                for (size_t j = 0; j < 16; j++) {
                    if (i + j < plen) fprintf(stderr, "%02x ", buf[po + i + j]);
                    else fprintf(stderr, "   ");
                }
                fprintf(stderr, " | ");
                for (size_t j = 0; j < 16 && i + j < plen; j++) {
                    uint8_t c = buf[po + i + j];
                    fputc((c >= 32 && c < 127) ? c : '.', stderr);
                }
                fprintf(stderr, "\n");
            }
        }

//         static void reasm_flush(int msgq_id, const char* ts)
//         {
//             if (g_reasm.blocks.empty())
//                 return;
//             dump_p25_udp_payload(g_reasm.blocks, msgq_id, ts, g_reasm.rid);
//             g_reasm.blocks.clear();
//             g_reasm.rid = 0;
//             g_reasm.last_ser = 0xff;
//         }


        void p25p1_fdma::process_TSBK(const bit_vector& fr, uint32_t fr_len) {
            uint8_t op, lb = 0;
            block_vector deinterleave_buf;
            d_stat_tsbk_attempted++;
            if (process_blocks(fr, fr_len, deinterleave_buf) == 0) {
                for (size_t j = 0; (j < deinterleave_buf.size()) && (lb == 0); j++) {
                    if (crc16(deinterleave_buf[j].data(), 12) != 0) {
                        /* Previously a silent return -- TSBK CRC failures
                         * had ZERO logging at any debug level, ever,
                         * unlike PDU headers which at least print
                         * unconditionally. TSBKs carry grants and
                         * pages -- exactly the events this whole
                         * investigation exists to not miss -- so a
                         * CRC-failed TSBK could be a lost page with
                         * literally no trace anywhere. Printing the raw
                         * bytes makes it visible and correlatable
                         * against a CAD reference, the same way
                         * PDU-level misses have been checked throughout
                         * this project. bytes[7:10] is where target_rid
                         * lives for grant/page opcodes specifically
                         * (matches parse_op25_tsbk's bit layout on the
                         * Python side) -- but the opcode itself is
                         * unverified when CRC has failed, so this is a
                         * plausible guess, not a confirmed field, unlike
                         * the PDU header case where the RID position is
                         * fixed regardless of fmt. */
                        uint32_t maybe_rid = ((uint32_t)deinterleave_buf[j][7] << 16) |
                                              ((uint32_t)deinterleave_buf[j][8] << 8)  |
                                               (uint32_t)deinterleave_buf[j][9];
                        fprintf(stderr, "%s TSBK CRC fail maybe_rid=%u (unverified, opcode-dependent) :",
                                logts.get(d_msgq_id), maybe_rid);
                        for (int i = 0; i < 12; i++)
                            fprintf(stderr, " %02x", deinterleave_buf[j][i]);
                        fprintf(stderr, "\n");
                        return;
                    }

                    if (j == 0) d_stat_tsbk_passed++;  // count once per TSBK call
                    lb = deinterleave_buf[j][0] >> 7;	// last block flag
                    op = deinterleave_buf[j][0] & 0x3f;	// opcode
                    process_duid(framer->duid, framer->nac, deinterleave_buf[j].data(), 10);

                    tsbk_export(logts.get(d_msgq_id), framer->nac, op, lb,
                               deinterleave_buf[j].data());

                    if (d_debug >= 10) {
                        fprintf (stderr, "%s NAC 0x%03x TSBK: op=%02x : %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x\n",
                                logts.get(d_msgq_id), framer->nac, op,
                                deinterleave_buf[j][0], deinterleave_buf[j][1], deinterleave_buf[j][2], deinterleave_buf[j][3],
                                deinterleave_buf[j][4], deinterleave_buf[j][5], deinterleave_buf[j][6], deinterleave_buf[j][7],
                                deinterleave_buf[j][8], deinterleave_buf[j][9], deinterleave_buf[j][10], deinterleave_buf[j][11]);
                    }
                }
            }
        }



        void p25p1_fdma::process_PDU(const bit_vector& fr, uint32_t fr_len) {
            uint8_t fmt, sap, blks, op = 0;
            block_vector deinterleave_buf;
            d_stat_pdu_attempted++;

            //int rc = process_blocks(fr, fr_len, deinterleave_buf);
            int rc = process_blocks(fr, fr_len, deinterleave_buf);
            fprintf(stderr, "%s PDU process_blocks rc=%d nblk=%zu fr_len=%u\n",
                    logts.get(d_msgq_id), rc, deinterleave_buf.size(), fr_len);
                    
            if (rc != 0 || fr_len > 400) {
                fprintf(stderr, "%s PDU LONG/FAIL hex:", logts.get(d_msgq_id));
                for (size_t b = 0; b < deinterleave_buf.size(); b++) {
                    fprintf(stderr, "  [");
                    for (int i = 0; i < 12; i++)
                        fprintf(stderr, "%02x", deinterleave_buf[b][i]);
                    fprintf(stderr, "]");
                }
                fprintf(stderr, "\n");
            }
            
            if (d_debug >= 1)
                fprintf(stderr, "%s PDU process_blocks rc=%d nblk=%zu\n",
                        logts.get(d_msgq_id), rc, deinterleave_buf.size());

            if (rc != 0 || deinterleave_buf.size() == 0)
                return;

            if (crc16(deinterleave_buf[0].data(), 12) != 0) {
                /* Header CRC failed, so these bytes aren't verified --
                 * but the RID field position is fixed regardless of
                 * whether the rest of the header is trustworthy, and
                 * printing it (clearly marked unverified) makes it much
                 * easier to spot a pattern -- e.g. the near-immediate
                 * CRC-failing repeat that follows a real delivery,
                 * worth digging into further. */
                uint32_t maybe_rid = ((uint32_t)deinterleave_buf[0][3] << 16) |
                                      ((uint32_t)deinterleave_buf[0][4] << 8)  |
                                       (uint32_t)deinterleave_buf[0][5];
                fprintf(stderr, "%s PDU header CRC fail nblk=%zu maybe_rid=%u (unverified, CRC failed) :",
                        logts.get(d_msgq_id), deinterleave_buf.size(), maybe_rid);
                for (int i = 0; i < 12; i++)
                    fprintf(stderr, " %02x", deinterleave_buf[0][i]);
                fprintf(stderr, "\n");
                return;
            }
            d_stat_pdu_passed++;

            fmt  = deinterleave_buf[0][0] & 0x1f;
            sap  = deinterleave_buf[0][1] & 0x3f;
            blks = deinterleave_buf[0][6] & 0x7f;

            {
                uint32_t rid = ((uint32_t)deinterleave_buf[0][3] << 16) |
                                ((uint32_t)deinterleave_buf[0][4] << 8) |
                                 (uint32_t)deinterleave_buf[0][5];
                /* fmt=0x03, blks=0 is a bare single-block frame with no
                 * confirmed data blocks -- structurally there's no IP/UDP
                 * payload here to show (that only exists once confirmed
                 * data blocks are present, handled separately in
                 * process_blocks() for fmt=0x16/0x17). This is very
                 * plausibly the SNDCP confirmed-delivery ack/response
                 * that follows a real ARS/TMS exchange -- same RID,
                 * arriving a few hundred ms later, different sap per
                 * transaction. Worth watching whether sap correlates
                 * consistently with which exchange (ARS vs TMS) it's
                 * acking. */
                if (fmt == 0x03 && blks == 0) {
                    fprintf(stderr, "%s ACK/RX rid=%u sap=%u fmt=0x%02x (no data blocks -- delivery ack/response, no IP/UDP to show)\n",
                            logts.get(d_msgq_id), rid, sap, fmt);
                }

                /* Every other CRC-passing header used to fall through to
                 * only the raw-hex line below with no readable rid= --
                 * meaning genuine, real over-the-air content could be
                 * logged in a form invisible to any rid= text search
                 * (including the tune-correlation analysis this project
                 * has been using to measure "silent" tunes). fmt=0x16/17
                 * still gets its own richer print from process_blocks;
                 * this covers everything else so nothing is ever
                 * captured-but-unlabeled again. */
                if (!(fmt == 0x03 && blks == 0) && fmt != 0x16 && fmt != 0x17)
                    fprintf(stderr, "%s PDU rid=%u fmt=0x%02x sap=%u blks=%u (other/unhandled fmt)\n",
                            logts.get(d_msgq_id), rid, fmt, sap, blks);
            }

            fprintf(stderr, "%s NAC 0x%03x PDU hex: fmt=0x%02x sap=%d blks=%d nblk=%zu :",
                    logts.get(d_msgq_id), framer->nac, fmt, sap, blks, deinterleave_buf.size());
            for (size_t b = 0; b < deinterleave_buf.size(); b++) {
                fprintf(stderr, "  [");
                for (int i = 0; i < 12; i++)
                    fprintf(stderr, "%02x", deinterleave_buf[b][i]);
                fprintf(stderr, "]");
            }
            fprintf(stderr, "\n");
            
            if (fmt == 0x16 || fmt == 0x17) {
                if (sap == 6)
                    reasm_flush(reasm, d_msgq_id, logts.get(d_msgq_id));
            }
            
            // ********
            /* rest of function unchanged (MBT sap==61, non-MBT ignored) */
                if ((sap == 61) && ((fmt == 0x17) || (fmt == 0x15))) { // Multi Block Trunking messages
                    if (blks >= deinterleave_buf.size())
                        return; // insufficient blocks available

                    uint32_t crc1 = crc32(deinterleave_buf[1].data(), ((blks * 12) - 4) * 8);
                    uint32_t crc2 = (deinterleave_buf[blks][8] << 24) + (deinterleave_buf[blks][9] << 16) +
                        (deinterleave_buf[blks][10] << 8) + deinterleave_buf[blks][11];

                    if (crc1 != crc2)
                        return; // payload crc check failed

                    process_duid(framer->duid, framer->nac, deinterleave_buf[0].data(), ((blks + 1) * 12) - 4);

                    if (d_debug >= 10) {
                        if (fmt == 0x15) {
                            op =   deinterleave_buf[1][0] & 0x3f; // Unconfirmed MBT format
                        } else if (fmt == 0x17) {
                            op =   deinterleave_buf[0][7] & 0x3f; // Alternate MBT format
                        }

                        char s0[40], s1[40], s2[40], s3[40];
                        sprintf(s0, "%02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x",
                                deinterleave_buf[0][0], deinterleave_buf[0][1], deinterleave_buf[0][2], deinterleave_buf[0][3],
                                deinterleave_buf[0][4], deinterleave_buf[0][5], deinterleave_buf[0][6], deinterleave_buf[0][7],
                                deinterleave_buf[0][8], deinterleave_buf[0][9], deinterleave_buf[0][10], deinterleave_buf[0][11]);
                        sprintf(s1, "%02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x",
                                deinterleave_buf[1][0], deinterleave_buf[1][1], deinterleave_buf[1][2], deinterleave_buf[1][3],
                                deinterleave_buf[1][4], deinterleave_buf[1][5], deinterleave_buf[1][6], deinterleave_buf[1][7],
                                deinterleave_buf[1][8], deinterleave_buf[1][9], deinterleave_buf[1][10], deinterleave_buf[1][11]);
                        sprintf(s2, "%02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x",
                                deinterleave_buf[2][0], deinterleave_buf[2][1], deinterleave_buf[2][2], deinterleave_buf[2][3],
                                deinterleave_buf[2][4], deinterleave_buf[2][5], deinterleave_buf[2][6], deinterleave_buf[2][7],
                                deinterleave_buf[2][8], deinterleave_buf[2][9], deinterleave_buf[2][10], deinterleave_buf[2][11]);
                        sprintf(s3, "%02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x",
                                deinterleave_buf[3][0], deinterleave_buf[3][1], deinterleave_buf[3][2], deinterleave_buf[3][3],
                                deinterleave_buf[3][4], deinterleave_buf[3][5], deinterleave_buf[3][6], deinterleave_buf[3][7],
                                deinterleave_buf[3][8], deinterleave_buf[3][9], deinterleave_buf[3][10], deinterleave_buf[3][11]);
                        fprintf (stderr, "%s NAC 0x%03x PDU:  fmt=%02x, op=0x%02x : %s %s %s %s\n",
                                logts.get(d_msgq_id), framer->nac, fmt, op, s0, s1, s2, s3);
                    }
                } else if (d_debug >= 10) {
                    fprintf(stderr, "%s NAC 0x%03x PDU:  non-MBT message ignored\n", logts.get(d_msgq_id), framer->nac);
                }

            }
        



        int p25p1_fdma::process_blocks(const bit_vector& fr, uint32_t& fr_len, block_vector& dbuf) {
            bit_vector bv;
            bv.reserve(fr_len >> 1);
            for (unsigned int d = 0; d < fr_len >> 1; d++) {
                if ((d + 1) % 36 == 0)
                    continue;
                bv.push_back(fr[d * 2]);
                bv.push_back(fr[d * 2 + 1]);
            }

            int bl_len = (int)((bv.size() - (48 + 64)) / 196);
            if (bl_len < 1)
                bl_len = 1;

            for (int bl_cnt = 0; bl_cnt < bl_len; bl_cnt++) {
                dbuf.push_back({0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0});
                if (block_deinterleave(bv, 48 + 64 + bl_cnt * 196, dbuf[bl_cnt].data()) != 0) {
                    fprintf(stderr, "%s process_blocks trellis1/2 fail blk=%d (kept)\n",
                            logts.get(d_msgq_id), bl_cnt);
                }
            }

            if (dbuf.size() >= 1) {
                const char* ts = logts.get(d_msgq_id);
                double now = logts.get_ts();

                if (crc16(dbuf[0].data(), 12) != 0) {
                    fprintf(stderr, "%s PDU header CRC fail nblk=%zu\n", ts, dbuf.size());

                    /* Header trellis/CRC failed, which normally means the
                     * whole burst -- header AND any confirmed data blocks
                     * after it -- gets dropped here, even when the later
                     * blocks decoded to real (non-zero) rate-3/4 content.
                     * Confirmed with captured bytes: bursts have shown up
                     * with an all-zero header/block1 but a clearly non-zero
                     * block2 sitting where a live confirmed data block
                     * belongs (leading byte matches the FSN pattern of
                     * genuine confirmed blocks), seconds into an already
                     * active session to a known RID. A header can fade out
                     * mid-burst without the data blocks that follow it
                     * fading too -- so if a data session is already active
                     * and recent, decode this burst's blocks against the
                     * *cached* RID rather than discarding them outright. */
                    if (bl_len > 1 && reasm.rid &&
                        (now - reasm.last_ts) <= REASM_WINDOW_SEC) {
                        /* No d_dwell_rid check anymore -- that guard existed
                         * only to protect against a stale RID left over from
                         * a PREVIOUS physical channel after a retune (see
                         * set_dwell_rid()'s comment). Fixed-frequency
                         * multi_rx.py operation with no external
                         * dwell-tracking feed removes that scenario
                         * entirely: this instance's reasm is per-channel
                         * (own member, not a shared global -- see RidReasm
                         * in p25p1_fdma.h) and this channel is never
                         * retuned, so reasm.rid can only ever have been set
                         * by real traffic actually heard on THIS frequency.
                         * The remaining, narrower risk -- a genuinely
                         * different RID's headerless burst landing on this
                         * same fixed channel within REASM_WINDOW_SEC of the
                         * cached one -- is accepted for now (per 2026-09-26
                         * decision to drop the Uniden CC monitor rather than
                         * keep it solely to arbitrate this edge case).
                         * set_dwell_rid()/d_dwell_rid are left in place,
                         * unused but harmless, in case that decision gets
                         * revisited later. */
                        uint8_t d34[32][18];
                        int n34 = 0;
                        memset(d34, 0, sizeof(d34));
                        for (int b = 1; b < bl_len && n34 < 32; b++) {
                            uint8_t blk[18];
                            memset(blk, 0, sizeof(blk));
                            if (block_deinterleave_34(bv, 48 + 64 + b * 196, blk) != 0)
                                continue;
                            bool allzero = true;
                            for (int i = 0; i < 18 && allzero; i++)
                                if (blk[i]) allzero = false;
                            if (allzero)
                                continue;   /* nothing decoded here, not a real block */
                            memcpy(d34[n34], blk, 18);
                            n34++;
                            fprintf(stderr, "%s SALVAGE blk%d rid=%u (headerless):", ts, b, reasm.rid);
                            for (int i = 0; i < 18; i++)
                                fprintf(stderr, " %02x", blk[i]);
                            fprintf(stderr, "\n");
                        }
                        if (n34 > 0)
                            reasm_burst(reasm, d_msgq_id, ts, reasm.rid, now, d34, n34);
                    } else if (bl_len > 1) {
                        /* No live session to attribute this to -- the case
                         * that swallows a page with zero trace today. The
                         * header is only how we NAME the burst; the rate-3/4
                         * data blocks after it are independently coded and
                         * decodable on their own regardless of whether the
                         * header survived. So decode them anyway and gate
                         * acceptance on the DATA looking real -- Viterbi
                         * cost (unchanged threshold), a sane serial, and an
                         * actual IPv4/UDP/TMS shape once reassembled --
                         * instead of gating on session state. Added
                         * 2026-09-30; see chat log for the false-positive
                         * vs missed-page tradeoffs this was built against,
                         * and why a block-level CRC check isn't part of
                         * the gate (tested empirically against 36k real
                         * accepted blocks -- doesn't validate, so it's not
                         * a real signal here). */

                        /* Ghost-burst guard, scoped to this branch only --
                         * doesn't touch the live-session path above. Large
                         * fake bursts (seen for real: nblk=20, header
                         * `76 c0 00 3c 00 00 00 00 00 00 00 00`) decode to
                         * a header whose only non-zero content is byte 0.
                         * Skip the Viterbi work entirely on those instead
                         * of burning cycles on every block for nothing. */
                        bool header_ghost = true;
                        for (int i = 1; i < 12 && header_ghost; i++)
                            if (dbuf[0][i]) header_ghost = false;

                        if (!header_ghost) {
                            uint8_t d34[32][18];
                            int n34 = 0;
                            memset(d34, 0, sizeof(d34));
                            bool sndcp_shape = false;

                            for (int b = 1; b < bl_len && n34 < 32; b++) {
                                uint8_t blk[18];
                                memset(blk, 0, sizeof(blk));
                                if (block_deinterleave_34(bv, 48 + 64 + b * 196, blk) != 0)
                                    continue;   // cost > 8, same threshold as always

                                bool allzero = true, allf5 = true;
                                for (int i = 0; i < 18; i++) {
                                    if (blk[i]) allzero = false;
                                    if (blk[i] != 0xf5) allf5 = false;
                                }
                                if (allzero || allf5)
                                    continue;   // nothing decoded / trailing filler

                                /* Real FSNs observed on this system run
                                 * 0-37; only 3 of 36,372 accepted blocks
                                 * ever exceeded 127, all three at the same
                                 * outlier value. Cheap, evidence-backed
                                 * sanity check -- not a CRC, just a range. */
                                if (blk[0] > 127)
                                    continue;

                                if (n34 > 0 && blk[0] == d34[n34-1][0])
                                    continue;   // exact repeat serial -- air retry

                                if (n34 == 0 && blk[2] == 0x01 && blk[3] == 0x03 && blk[4] == 0xf1) {
                                    /* SNDCP-ctrl shape (matches the real
                                     * sap=6 case on rid=4116652) -- flush,
                                     * don't stitch this onto a fake TMS
                                     * message. */
                                    sndcp_shape = true;
                                    break;
                                }

                                memcpy(d34[n34], blk, 18);
                                n34++;
                            }

                            if (n34 > 0 && !sndcp_shape) {
                                /* Local, disposable buffer -- never touches
                                 * reasm.buf/reasm.rid, so a wrong guess here
                                 * can't corrupt an actual live session. */
                                std::vector<uint8_t> scratch;
                                for (int i = 0; i < n34; i++)
                                    scratch.insert(scratch.end(), d34[i] + 2, d34[i] + 18);

                                /* Same IPv4 signature reasm_dump() keys on,
                                 * bounded to a few bytes of slack in case
                                 * the first accepted block isn't block 1. */
                                int off = -1;
                                for (size_t i = 0; i + 20 <= scratch.size() && i < 4; i++) {
                                    if (scratch[i] == 0x45) { off = (int)i; break; }
                                }

                                if (off >= 0 && (int)scratch.size() - off >= 20) {
                                    /* Never a data block's bytes as RID --
                                     * that mistake's already been made and
                                     * fixed once in this file. Try the
                                     * original 12-byte header's RID field
                                     * (unverified, but it's still the right
                                     * field, just an unverified header), or
                                     * fall back to 0 and export anyway --
                                     * a page with no RID beats a silent
                                     * drop. */
                                    bool header_nonzero = dbuf[0][3] || dbuf[0][4] || dbuf[0][5];
                                    uint32_t maybe_rid = header_nonzero ?
                                        (((uint32_t)dbuf[0][3] << 16) |
                                         ((uint32_t)dbuf[0][4] << 8)  |
                                          (uint32_t)dbuf[0][5]) : 0;

                                    fprintf(stderr,
                                        "%s [%d] SALVAGE_TMS rid=%u (unverified -- no live "
                                        "session, header CRC failed, %d/%d blocks accepted)\n",
                                        ts, d_msgq_id, maybe_rid, n34, bl_len - 1);
                                    reasm_print_ip(d_msgq_id, ts, scratch.data() + off,
                                                    (int)scratch.size() - off, maybe_rid, true);
                                }
                            }
                        }
                    }
                } else {
                    uint8_t fmt0 = dbuf[0][0] & 0x1f;
                    uint8_t sap0 = dbuf[0][1] & 0x3f;
                    uint32_t rid = ((uint32_t)dbuf[0][3] << 16) |
                                   ((uint32_t)dbuf[0][4] << 8)  |
                                    (uint32_t)dbuf[0][5];

                    if (reasm.rid && (now - reasm.last_ts) > REASM_WINDOW_SEC)
                        reasm_flush(reasm, d_msgq_id, ts);

                    if (fmt0 == 0x16 || fmt0 == 0x17) {
                        uint8_t blks_hdr = dbuf[0][6] & 0x7f;
                        uint8_t d34[32][18];
                        int n34 = 0;
                        memset(d34, 0, sizeof(d34));
                        for (int b = 1; b < bl_len && n34 < 32; b++) {
                            uint8_t blk[18];
                            memset(blk, 0, sizeof(blk));
                            if (block_deinterleave_34(bv, 48 + 64 + b * 196, blk) != 0) {
                                fprintf(stderr, "%s CONFIRMED blk%d fail rid=%u\n", ts, b, rid);
                                continue;
                            }
                            memcpy(d34[n34], blk, 18);
                            n34++;
                            fprintf(stderr, "%s CONFIRMED blk%d rid=%u:", ts, b, rid);
                            for (int i = 0; i < 18; i++)
                                fprintf(stderr, " %02x", blk[i]);
                            fprintf(stderr, "\n");

                            if (b > blks_hdr) {
                                /* Genuinely beyond what THIS header
                                 * declared -- not just past the old
                                 * header+3 baseline, which fires on every
                                 * legitimate 4th+ block of a message that
                                 * says it needs one (false-positived on
                                 * the real "AHS_Messaging_A..." recovery).
                                 * This is the actual leak signature: a
                                 * block index the header never promised,
                                 * which is what 0x3ED096 = 4116630 looked
                                 * like during the 3600-bit experiment. */
                                uint32_t maybe_rid = ((uint32_t)blk[3] << 16) |
                                                      ((uint32_t)blk[4] << 8)  |
                                                       (uint32_t)blk[5];
                                fprintf(stderr,
                                    "%s *** EXTRA BLOCK blk%d (beyond blks_hdr=%u) rid=%u -- "
                                    "check for leak: bytes[3:6]=%06x (as RID: %u)\n",
                                    ts, b, blks_hdr, rid, maybe_rid, maybe_rid);
                            }
                        }
                        fprintf(stderr,
                            "%s PDU hdr fmt=0x%02x sap=%u rid=%u blks_hdr=%u n34=%d fr_len=%u\n",
                            ts, fmt0, sap0, rid, blks_hdr, n34, fr_len);
                        
                        if (sap0 == 6) {
                            if (reasm.rid)
                                reasm_flush(reasm, d_msgq_id, ts);
                            fprintf(stderr, "%s SNDCP ctrl rid=%u n34=%d\n", ts, rid, n34);
                        } else if (sap0 == 0) {
                            reasm_burst(reasm, d_msgq_id, ts, rid, now, d34, n34);
                            if (bl_len >= 4 || fr_len >= 900) {
                                /* HOLD no longer fires from here -- frame
                                 * length/block count doesn't distinguish a
                                 * genuinely unfinished IP datagram from a
                                 * routine 3-block poke (every poke is this
                                 * shape too). The hold trigger now lives in
                                 * reasm_dump(), gated on the actual IPv4
                                 * length vs bytes in hand, which is known
                                 * from block 1 of the first burst -- no
                                 * need to wait for reassembly to finish.
                                 * dump_pdu_burst() below is just the /tmp
                                 * diagnostic dump; unrelated to holding. */
                                dump_pdu_burst(ts, rid, fr_len,
                                               dbuf[0].data(), bv, bl_len,
                                               d34, n34);
                            }
                        }
                    }
                }
            }
            
            return (dbuf.size() > 0) ? 0 : -1;
            }

        void p25p1_fdma::process_voice(const bit_vector& A, const frame_type fr_type) {
            if (d_do_imbe || d_do_audio_output) {
                if (encrypted()) {
                    crypt_algs.prepare(ess_algid, ess_keyid, PT_P25_PHASE1, ess_mi);
                }

                for(size_t i = 0; i < nof_voice_codewords; ++i) {
                    voice_codeword cw(voice_codeword_sz);
                    uint32_t E0, ET;
                    uint32_t u[8];
                    char s[128];
                    bool audio_valid = !encrypted();
                    size_t errs = 0;
                    imbe_deinterleave(A, cw, i);

                    errs = imbe_header_decode(cw, u[0], u[1], u[2], u[3], u[4], u[5], u[6], u[7], E0, ET);

                    if (d_debug >= 9) {
                        packed_codeword p_cw;
                        if (!encrypted()) {
                            imbe_pack(p_cw, u[0], u[1], u[2], u[3], u[4], u[5], u[6], u[7]);
                            sprintf(s,"%02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x",
                                    p_cw[0], p_cw[1], p_cw[2], p_cw[3], p_cw[4], p_cw[5],
                                    p_cw[6], p_cw[7], p_cw[8], p_cw[9], p_cw[10]);
                            fprintf(stderr, "%s IMBE (CLEARTEXT) %s errs %lu\n", logts.get(d_msgq_id), s, errs); // print to log in one operation
                        } else {
                            imbe_pack(p_cw, u[0], u[1], u[2], u[3], u[4], u[5], u[6], u[7]);
                            sprintf(s,"%02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x",
                                    p_cw[0], p_cw[1], p_cw[2], p_cw[3], p_cw[4], p_cw[5],
                                    p_cw[6], p_cw[7], p_cw[8], p_cw[9], p_cw[10]);
                            fprintf(stderr, "%s IMBE (CIPHERTXT) %s errs %lu\n", logts.get(d_msgq_id), s, errs); // print to log in one operation

                        }
                    }

                    // Silence unencrypted traffic when crypt_behavior = -1
                    if (!encrypted() && d_behavior == -1) {
                        return;
                        // packed_codeword p_cw;
                        // imbe_pack(p_cw, u[0], u[1], u[2], u[3], u[4], u[5], u[6], u[7]);
                        // p_cw[0] = 0x04;
                        // p_cw[1] = 0x0C;
                        // p_cw[2] = 0xFD;
                        // p_cw[3] = 0x7B;
                        // p_cw[4] = 0xFB;
                        // p_cw[5] = 0x7D;
                        // p_cw[6] = 0xF2;
                        // p_cw[7] = 0x7B;
                        // p_cw[8] = 0x3D;
                        // p_cw[9] = 0x9E;
                        // p_cw[10] = 0x44;
                        // imbe_unpack(p_cw, u[0], u[1], u[2], u[3], u[4], u[5], u[6], u[7]);
                    }

                    if (encrypted()) {
                        packed_codeword ciphertext;
                        imbe_pack(ciphertext, u[0], u[1], u[2], u[3], u[4], u[5], u[6], u[7]);
                        audio_valid = crypt_algs.process(ciphertext, fr_type, i);
                        // sprintf(s,"%02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x",
//                                 ciphertext[0], ciphertext[1], ciphertext[2], ciphertext[3], ciphertext[4], ciphertext[5],
//                                 ciphertext[6], ciphertext[7], ciphertext[8], ciphertext[9], ciphertext[10]);
//                         fprintf(stderr, "%s IMBE (PLAINTEXT) %s errs %lu\n", logts.get(d_msgq_id), s, errs); // print to log in one operation
                        imbe_unpack(ciphertext, u[0], u[1], u[2], u[3], u[4], u[5], u[6], u[7]);
                    }

                    if (d_do_audio_output && audio_valid) {
                        software_decoder.decode_fullrate(u[0], u[1], u[2], u[3], u[4], u[5], u[6], u[7], E0, ET);
                        audio_samples *samples = software_decoder.audio();
                        for (int i=0; i < SND_FRAME; i++) {
                            if (samples->size() > 0) {
                                snd[i] = (int16_t)(samples->front());
                                samples->pop_front();
                            } else {
                                snd[i] = 0;
                            }
                        }
                        if (op25audio.enabled()) {      // decoded audio goes out via UDP (normal code path)
                            op25audio.send_audio(snd, SND_FRAME * sizeof(int16_t));
                        } else {                        // decoded audio back to gnuradio (still supported?)
                            for (int i = 0; i < SND_FRAME; i++) {
                                output_queue.push_back(snd[i]);
                            }
                        }
                    }

                    if (d_do_output && !d_do_audio_output) { // ugh! - legacy wireshark support
                        sprintf(s, "%03x %03x %03x %03x %03x %03x %03x %03x\n", u[0], u[1], u[2], u[3], u[4], u[5], u[6], u[7]);
                        for (size_t j=0; j < strlen(s); j++) {
                            output_queue.push_back(s[j]);
                        }
                    }
                }
            }
        }

        void p25p1_fdma::reset_timer() {
            qtimer.reset();
        }

        void p25p1_fdma::call_end() {
            if (d_do_audio_output)
                op25audio.send_audio_flag(op25_audio::DRAIN);
            reset_ess();
        }

        void p25p1_fdma::crypt_reset() {
            crypt_algs.reset();
        }

        void p25p1_fdma::crypt_key(uint16_t keyid, uint8_t algid, const std::vector<uint8_t> &key) {
            crypt_algs.key(keyid, algid, key);
        }

        void p25p1_fdma::send_msg(const std::string msg_str, long msg_type) {
            if (!d_do_msgq)
                return;

            gr::message::sptr msg = gr::message::make_from_string(msg_str, get_msg_type(PROTOCOL_P25, msg_type), (d_msgq_id << 1), logts.get_ts());
            if (!d_msg_queue->full_p())
                d_msg_queue->insert_tail(msg);
        }

        void p25p1_fdma::process_frame() {
            // Debug looking for other data
//             fprintf(stderr, "RDBG: %s NAC 0x%03x DUID=0x%02x flen=%u\n",
//                 logts.get(d_msgq_id), framer->nac, framer->duid, framer->frame_size);
            // extract additional signalling information and voice codewords
            switch(framer->duid) {
                case 0x00:
                    process_HDU(framer->frame_body);
                    break;
                case 0x03:
                    process_TDU3();
                    break;
                case 0x05:
                    process_LDU1(framer->frame_body);
                    break;
                case 0x07:
                    process_TSBK(framer->frame_body, framer->frame_size);
                    break;
                case 0x0a:
                    process_LDU2(framer->frame_body);
                    break;
                case 0x0c:
                    process_PDU(framer->frame_body, framer->frame_size);
                    break;
                case 0x0f:
                    process_TDU15(framer->frame_body);
                    break;
                default:
                    fprintf(stderr, "RDBG: %s unknown DUID 0x%02x\n",
                        logts.get(d_msgq_id), framer->duid);
                    break;
            }

            if (!d_do_imbe) { // send raw frame to wireshark
                              // pack the bits into bytes, MSB first
                size_t obuf_ct = 0;
                uint8_t obuf[P25_VOICE_FRAME_SIZE/2];
                for (uint32_t i = 0; i < framer->frame_size; i += 8) {
                    uint8_t b = 
                        (framer->frame_body[i+0] << 7) +
                        (framer->frame_body[i+1] << 6) +
                        (framer->frame_body[i+2] << 5) +
                        (framer->frame_body[i+3] << 4) +
                        (framer->frame_body[i+4] << 3) +
                        (framer->frame_body[i+5] << 2) +
                        (framer->frame_body[i+6] << 1) +
                        (framer->frame_body[i+7]     );
                    obuf[obuf_ct++] = b;
                }
                op25audio.send_to(obuf, obuf_ct);

                if (d_do_output) {
                    for (size_t j=0; j < obuf_ct; j++) {
                        output_queue.push_back(obuf[j]);
                    }
                }
            }
        }

        // Construct a frame one symbol at a time (used by rx.py)
        void p25p1_fdma::rx_sym (const uint8_t *syms, int nsyms) {
            for (int i1 = 0; i1 < nsyms; i1++) {
                if(framer->rx_sym(syms[i1])) {   // complete frame was detected
                    if (framer->nac == 0) {  // discard frame if NAC is invalid
                        continue;
                    }

                    process_frame();
                }  // end of complete frame
            }
            check_timeout();
        }

        // Load a frame starting with NID block (used by multi_rx.py)
        uint32_t p25p1_fdma::load_nid(const uint8_t *syms, int nsyms, const uint64_t fs) {
            uint32_t fr_len = framer->load_nid(syms, nsyms, fs);
            check_timeout();
            return fr_len;
        }

        // Load remainder of frame body (used by multi_rx.py)
        bool p25p1_fdma::load_body(const uint8_t *syms, int nsyms) {
            bool rc = framer->load_body(syms, nsyms);
            if (rc) {
                process_frame();
            }
            check_timeout();
            return rc;
        }

        // Check for timer expiry
        void p25p1_fdma::check_timeout() {
            if (d_do_msgq) {
                // check for timeout
                if (qtimer.expired()) {
                    if (d_debug >= 10)
                        fprintf(stderr, "%s p25p1_fdma::check_timeout: expired\n", logts.get(d_msgq_id));

                    if (d_do_audio_output) {
                        op25audio.send_audio_flag(op25_audio::DRAIN);
                    }

                    qtimer.reset();
                    d_stat_timeouts++;
                    gr::message::sptr msg = gr::message::make(get_msg_type(PROTOCOL_P25, M_P25_TIMEOUT), (d_msgq_id << 1), logts.get_ts());
                    if (!d_msg_queue->full_p())
                        d_msg_queue->insert_tail(msg);
                }
            }
        }

    }  // namespace
}  // namespace
