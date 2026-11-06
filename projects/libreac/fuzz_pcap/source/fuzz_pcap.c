// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>
// Modified by Theorem Labs, 2026-10-25: a modified copy of fuzz/fuzz_pcap.c at libreac 9ed322ef.

/* libFuzzer harness: THE PCAP READER (src/pcap_source.c), the door every offline
 * capture comes in through before a frame decoder sees it.
 *
 * pcap_source_open() takes a path and fopen()s it. A harness may open no file but
 * its input, so this one is linked with -Wl,--wrap=fopen: every fopen() in the
 * program reaches __wrap_fopen below, which answers the one path FUZZ_PCAP_PATH
 * with fmemopen() over the input and hands every other path to the real fopen.
 * The library is untouched, and the reader runs its own header and record code
 * over exactly the bytes the fuzzer chose. The OSS Verify build
 * (projects/libreac/build.sh) makes the same redirection by name, not with
 * --wrap: only the reader's fopen reaches this function.
 *
 * Input:  [0]   the capacity of the record buffer, in units of 8 bytes (0..2040)
 *         [1..] the pcap file: global header, then records
 *
 * The record buffer is its own allocation of exactly that capacity (1 byte when the
 * capacity is 0), so the reader filling a byte past it is a sanitizer report.
 *
 * Properties, each an abort():
 *   - open accepts exactly the two classic magics, and a reader that failed to open
 *     holds no stream;
 *   - a record handed back fits the caller's buffer, and reading stops (EOF or
 *     error) within one record per 16 bytes of the file after its header;
 *   - the reader hands back each record of the file that fits the buffer, in file
 *     order, and skips the others and every record of 0 bytes; the walk ends with
 *     0 exactly at the end of the file (pcap_source.h: 0 means the end of the file
 *     and nothing else) and with -1 on a cut record. One case that the reader has
 *     today is accepted: with a buffer of 0 bytes a record with a body gives -1;
 *   - an 802.1Q tag is stripped exactly when the record carried one: the frame
 *     comes back four bytes shorter with the tag's VID on the source;
 *   - the timestamp of each record handed back is the record header's seconds and
 *     microseconds;
 *   - a closed reader holds no stream and answers -1; a reopened reader asked for
 *     no timestamp starts again with the same first answer.
 */
#define _POSIX_C_SOURCE 200809L   /* fmemopen */

#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <reac/pcap_source.h>

#include "fuzz.h"

#define FUZZ_PCAP_PATH "<fuzz-input>"

static const uint8_t *g_file;
static size_t g_file_len;

FILE *__real_fopen(const char *path, const char *mode);
FILE *__wrap_fopen(const char *path, const char *mode);

FILE *__wrap_fopen(const char *path, const char *mode)
{
	if (path && strcmp(path, FUZZ_PCAP_PATH) == 0) {
		/* fmemopen refuses a zero-length buffer: an empty input cannot be opened,
		 * which is what an empty file's missing header earns it anyway. */
		if (g_file_len == 0)
			return NULL;
		return fmemopen((void *)g_file, g_file_len, mode);
	}
	return __real_fopen(path, mode);
}

static uint32_t rd32(const uint8_t *p, int swap)
{
	uint32_t v = (uint32_t)p[0] | (uint32_t)p[1] << 8 | (uint32_t)p[2] << 16 |
	             (uint32_t)p[3] << 24;
	return swap ? __builtin_bswap32(v) : v;
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	if (size >= FUZZ_INPUT_MAX)
		return 0;
	struct fuzz_in in = fuzz_in(data, size);
	size_t cap = (size_t)fuzz_u8(&in) * 8;
	g_file_len = fuzz_take(&in, in.n, &g_file);
	/* A private copy, so the reader works on bytes nothing else aliases. */
	uint8_t *file = fuzz_dup(g_file, g_file_len);
	g_file = file;

	struct pcap_source ps;
	memset(&ps, 0xa5, sizeof ps);
	int r = pcap_source_open(&ps, FUZZ_PCAP_PATH);
	uint32_t magic = g_file_len >= 4 ? rd32(file, 0) : 0;
	int good = g_file_len >= 24 && (magic == 0xA1B2C3D4u || magic == 0xD4C3B2A1u);
	/* Open accepts a file of at least 24 bytes with one of the two classic magics,
	 * and refuses all other files.
	 * mutant: src/pcap_source.c:38 `magic == PCAP_MAGIC_SWAP` -> `magic == PCAP_MAGIC_SWAP + 1`
	 * input: fixtures-swapped
	 * mutant: src/pcap_source.c:36 `magic == PCAP_MAGIC` -> `magic == PCAP_MAGIC || magic == 0x0A0D0D0Au`
	 * input: pcapng-refused */
	if (r != (good ? 0 : -1))
		abort();
	if (r != 0) {
		/* A reader that failed to open holds no stream.
		 * mutant: src/pcap_source.c:42 `ps->f = NULL;` -> ``
		 * input: pcapng-refused
		 * mutant: src/pcap_source.c:31 `ps->f = NULL;` -> ``
		 * input: half-global-header */
		if (ps.f != NULL)
			abort();
		free(file);
		return 0;
	}
	/* The reader swaps the record headers exactly when the magic is the swapped one.
	 * mutant: src/pcap_source.c:39 `ps->swapped = 1;` -> `ps->swapped = 0;`
	 * input: fixtures-swapped */
	if (ps.swapped != (magic == 0xD4C3B2A1u))
		abort();

	uint8_t *buf = malloc(cap ? cap : 1);
	/* not a property: malloc failed, so there is no record buffer to test. */
	if (!buf)
		abort();
	/* The harness walks the same file alongside the reader to know what each record
	 * should come back as; it never decides anything the reader then has to agree to
	 * except the record the reader itself says it returned. */
	size_t at = 24;
	long n;
	long first = 0;   /* the first answer of the reader */
	size_t calls = 0;
	uint64_t ts = ~(uint64_t)0;
	while ((n = pcap_source_next(&ps, buf, cap, &ts)) > 0) {
		/* Each record handed back takes at least its 16-byte header from the file
		 * after the 24-byte global header (open succeeded, so the file has it).
		 * mutant: src/pcap_source.c:104 `return (long)incl;` -> `return (fseek(ps->f, -16 - (long)incl, SEEK_CUR), (long)incl);`
		 * input: two-equal-records */
		if (++calls > (g_file_len - 24) / 16)
			abort();
		if (calls == 1)
			first = n;
		/* A record handed back fits the caller's buffer. The record is the change
		 * of fuzz/sabotage/pcap.patch (a record of cap + 1 bytes is read, not
		 * skipped). The ASan builds can report the one-byte write in fread first.
		 * mutant: src/pcap_source.c:68 `incl > cap` -> `incl > cap + 1`
		 * input: record-one-byte-over-cap */
		if ((size_t)n > cap)
			abort();
		/* Skip the records the reader skipped: those larger than the buffer, and
		 * those of 0 bytes. */
		uint32_t incl;
		for (;;) {
			/* The reader returned a record the file holds.
			 * mutant: src/pcap_source.c:104 `return (long)incl;` -> `return (fseek(ps->f, -16 - (long)incl, SEEK_CUR), (long)incl);`
			 * input: skipped-then-small */
			if (at + 16 > g_file_len)
				abort();
			incl = rd32(file + at + 8, ps.swapped);
			if (incl != 0 && incl <= cap)
				break;
			at += 16 + (size_t)incl;
		}
		const uint8_t *rec = file + at + 16;
		/* The record handed back has its whole body in the file.
		 * mutant: src/pcap_source.c:86 `fread(buf, 1, incl, ps->f) != incl` -> `fread(buf, 1, incl, ps->f) == 0`
		 * input: snaplen-oversized-truncated */
		if (at + 16 + incl > g_file_len)
			abort();
		/* The source keeps the record header's original length.
		 * mutant: src/pcap_source.c:67 `ph + 12` -> `ph + 8`
		 * input: snaplen-oversized-truncated */
		if (ps.last_orig_len != rd32(file + at + 12, ps.swapped))
			abort();
		int tagged = incl >= 18 && rec[12] == 0x81 && rec[13] == 0x00;
		/* The source says tagged exactly when the record carried an 802.1Q tag.
		 * mutant: src/pcap_source.c:97 `ps->last_vlan_tagged = 1;` -> `ps->last_vlan_tagged = 0;`
		 * input: box-0832-vlan13
		 * mutant: src/pcap_source.c:94 `ps->last_vlan_tagged = 0;` -> `ps->last_vlan_tagged = 1;`
		 * input: fixtures */
		if (ps.last_vlan_tagged != tagged)
			abort();
		if (tagged) {
			/* A tagged record comes back four bytes shorter: the MAC addresses, then
			 * the rest of the frame after the tag, and the tag's VID on the source.
			 * mutant: src/pcap_source.c:100 `incl -= 4;` -> `incl -= 3;`
			 * input: box-0832-vlan13
			 * mutant: src/pcap_source.c:99 `memmove(buf + 12,` -> `memmove(buf + 8,`
			 * input: box-0832-vlan13
			 * mutant: src/pcap_source.c:99 `incl - 16` -> `incl - 17`
			 * input: box-0832-vlan13
			 * mutant: src/pcap_source.c:98 `| buf[15]` -> `| buf[14]`
			 * input: box-0832-vlan13 */
			if ((size_t)n != incl - 4 || memcmp(buf, rec, 12) != 0 ||
			    memcmp(buf + 12, rec + 16, incl - 16) != 0 ||
			    ps.last_vlan_id != (((rec[14] << 8) | rec[15]) & 0x0fff))
				abort();
		} else {
			/* An untagged record comes back as it is in the file.
			 * mutant: src/pcap_source.c:104 `return (long)incl;` -> `return (long)incl - 1;`
			 * input: fixtures
			 * mutant: src/pcap_source.c:86 `fread(buf, 1, incl, ps->f) != incl` -> `fread(buf, 1, incl, ps->f) != incl || (buf[0] ^= 1, 0)`
			 * input: fixtures */
			if ((size_t)n != incl || memcmp(buf, rec, incl) != 0)
				abort();
		}
		/* The timestamp of each record handed back is the record header's seconds
		 * times 10^6 plus its microseconds.
		 * mutant: src/pcap_source.c:103 `+ usec;` -> `+ usec + (ftell(ps->f) > 4096);`
		 * input: fixtures
		 * mutant: src/pcap_source.c:60 `rd_u32(ph + 4, ps->swapped)` -> `rd_u32(ph + 4, 0)`
		 * input: fixtures-swapped */
		if (ts != (uint64_t)rd32(file + at, ps.swapped) * 1000000ull +
		              rd32(file + at + 4, ps.swapped))
			abort();
		ts = ~(uint64_t)0;
		at += 16 + incl;
	}
	if (calls == 0)
		first = n;
	/* The walk ends with 0 (end of file) or -1 (error).
	 * mutant: src/pcap_source.c:58 `return -1;` -> `return -2;`
	 * input: half-record-header */
	if (n < -1)
		abort();
	{
		long want;
		size_t e = at;
		for (;;) {
			if (e == g_file_len) {
				want = 0;
				break;
			}
			if (e + 16 > g_file_len) {
				want = -1;
				break;
			}
			uint32_t len = rd32(file + e + 8, ps.swapped);
			if (len == 0) {
				e += 16;
				continue;
			}
			if (len <= cap) {
				want = e + 16 + (size_t)len <= g_file_len ? (long)len : -1;
				break;
			}
			if (cap == 0 || e + 16 + (size_t)len > g_file_len) {
				want = -1;
				break;
			}
			e += 16 + (size_t)len;
		}
		/* The walk ended where the file says it must. The loop above goes past the records
		 * that do not fit the buffer, as the reader does. At the end of the file, the answer is 0.
		 * A part of a record header, or a body that the file cuts, gives -1. The
		 * reader cannot skip a record with a buffer of 0 bytes, so that gives -1. A
		 * record of 0 bytes is skipped, as pcap_source.h says: 0 is the end of the
		 * file only. A complete record of more bytes that fits must have come back,
		 * so then no answer is correct (want is its length, and n is not more than 0).
		 * contract: include/reac/pcap_source.h, pcap_source_next ("0 means the end of
		 * the file and nothing else").
		 * mutant: src/pcap_source.c:55 `got == 0` -> `got <= 16`
		 * input: fixtures
		 * mutant: src/pcap_source.c:87 `return -1;` -> `return 0;`
		 * input: snaplen-oversized-truncated
		 * mutant: src/pcap_source.c:81 `return -1;` -> `return 0;`
		 * input: oversized-cut
		 * mutant: src/pcap_source.c:65 `incl == 0` -> `0`
		 * input: empty-record-then-frame */
		if (n != want)
			abort();
	}

	/* Once more from the top, with no timestamp asked for. */
	pcap_source_close(&ps);
	/* A closed reader holds no stream.
	 * mutant: src/pcap_source.c:112 `ps->f = NULL;` -> ``
	 * input: fixtures */
	if (ps.f != NULL)
		abort();
	/* A closed reader opens again.
	 * mutant: src/pcap_source.c:26 `!ps->f` -> `!ps->f || ps->swapped == 1`
	 * input: fixtures-swapped */
	if (pcap_source_open(&ps, FUZZ_PCAP_PATH) != 0)
		abort();
	/* The reopened reader, asked for no timestamp, gives the same first answer as
	 * the first walk gave.
	 * mutant: src/pcap_source.c:104 `return (long)incl;` -> `return (long)incl - !ts_usec;`
	 * input: fixtures */
	if (pcap_source_next(&ps, buf, cap, NULL) != first)
		abort();
	pcap_source_close(&ps);
	/* A closed reader answers -1, safely.
	 * mutant: src/pcap_source.c:51 `return -1;` -> `return 0;`
	 * input: header-only */
	if (pcap_source_next(&ps, buf, cap, NULL) != -1)
		abort();
	free(buf);
	free(file);
	return 0;
}
