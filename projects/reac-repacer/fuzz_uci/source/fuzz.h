// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>

/* What the harnesses of fuzz/ share: the REAC frame as the protocol lays it out,
 * written down here and never taken from libreac's or this tree's headers, so a
 * check compares the reader with the wire and not with itself; and the copies a
 * reader is handed. Nothing here reads a clock, the environment, a file or the
 * network, or starts a thread. */
#ifndef REPACE_FUZZ_H
#define REPACE_FUZZ_H

#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* The driver refuses a file of 64 MiB or more; so does each harness. */
#define FUZZ_INPUT_MAX ((size_t)64 << 20)

/* The REAC frame. contract: include/repace_wire.h:9-17 (the frame, as the daemon
 * reads it), and <reac/reac_braid.h>'s description of the braid. */
#define W_TYPE_HI      12      /* the EtherType, big-endian */
#define W_COUNTER      14      /* the frame counter, little-endian */
#define W_KIND         16      /* the frame type, 00 00 for audio */
#define W_AUDIO        50      /* the audio region */
#define W_OVERHEAD     52      /* the 50-byte header and the 2-byte end marker */
#define W_PER_CH       36      /* 12 samples x 3 bytes, per channel */
#define W_SAMPLES      12      /* time-samples per frame, at every rate */
#define W_MAX_CH       40      /* the downstream broadcast's width */
#define W_RESIDUE      2       /* FCS residue some capture paths leave */

/* The daemon's receive buffer: a frame reaches a reader as at most this many
 * bytes. contract: tools/reac_repacer.c `#define SLOT_SZ   1600` (recvfrom into
 * buf[SLOT_SZ] hands a longer frame over cut to its first 1600 bytes). */
#define W_RECV_MAX     1600

static inline int w_is_reac(const uint8_t *f, size_t at)
{
	return f[at] == 0x88 && f[at + 1] == 0x19;
}

static inline int w_is_tag(const uint8_t *f)
{
	return f[12] == 0x81 && f[13] == 0x00;
}

static inline int w_is_audio(const uint8_t *f)
{
	return f[16] == 0x00 && f[17] == 0x00;
}

/* The channel width of a frame of len bytes, by the frame law: the even widths
 * 2..40, each at 52 + nch * 36 bytes, or two bytes more with the FCS residue. -1
 * for every other length. A table walk, not the reader's arithmetic. */
static inline int w_width(long len)
{
	for (int nch = 2; nch <= W_MAX_CH; nch += 2) {
		long clean = W_OVERHEAD + (long)nch * W_PER_CH;
		if (len == clean || len == clean + W_RESIDUE)
			return nch;
	}
	return -1;
}

/* The braid, as <reac/reac_braid.h> describes it: per time-sample s, the channel
 * pair (2k, 2k+1) packed big-endian s24, even channel first, as six bytes
 * A2 A1 A0 B2 B1 B0, then each 16-bit word byte-swapped: A1 A2 B2 A0 B0 B1, at
 * region offset (s * nch + 2k) * 3. These put and get one channel's sample by
 * building that pair group, not by reac_braid_pos(). */
static inline size_t w_group(int s, int ch, int nch)
{
	return W_AUDIO + (size_t)(s * nch + (ch & ~1)) * 3;
}

static inline void w_put(uint8_t *f, int s, int ch, int nch, int32_t v)
{
	uint8_t be[6], *g = f + w_group(s, ch, nch);
	/* the pair as it stands, un-swapped to big-endian */
	for (int w = 0; w < 3; w++) {
		be[2 * w] = g[2 * w + 1];
		be[2 * w + 1] = g[2 * w];
	}
	int at = (ch & 1) ? 3 : 0;
	be[at] = (uint8_t)((uint32_t)v >> 16);
	be[at + 1] = (uint8_t)((uint32_t)v >> 8);
	be[at + 2] = (uint8_t)v;
	for (int w = 0; w < 3; w++) {
		g[2 * w] = be[2 * w + 1];
		g[2 * w + 1] = be[2 * w];
	}
}

static inline int32_t w_get(const uint8_t *f, int s, int ch, int nch)
{
	const uint8_t *g = f + w_group(s, ch, nch);
	uint8_t be[6];
	for (int w = 0; w < 3; w++) {
		be[2 * w] = g[2 * w + 1];
		be[2 * w + 1] = g[2 * w];
	}
	int at = (ch & 1) ? 3 : 0;
	uint32_t u = (uint32_t)be[at] << 16 | (uint32_t)be[at + 1] << 8 | be[at + 2];
	return u >= 0x800000u ? (int32_t)u - 0x1000000 : (int32_t)u;
}

/* An exact-size heap copy of n bytes, so a read past them is AddressSanitizer's. */
static inline uint8_t *fuzz_dup(const uint8_t *p, size_t n)
{
	uint8_t *b = malloc(n ? n : 1);

	/* not a property: the harness's own allocation failed */
	if (!b)
		abort();
	if (n)
		memcpy(b, p, n);
	return b;
}

/* The little-endian integer of the 4 bytes at p. */
static inline uint32_t fuzz_le32(const uint8_t *p)
{
	return (uint32_t)p[0] | (uint32_t)p[1] << 8 | (uint32_t)p[2] << 16 | (uint32_t)p[3] << 24;
}

#endif /* REPACE_FUZZ_H */
