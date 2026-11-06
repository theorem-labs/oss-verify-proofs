// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>

/* What every libFuzzer harness in fuzz/ shares: a cursor over the input, the input-size
 * refusal, and the exact-size copy that lets the sanitizer see a read one byte past a frame.
 *
 * The cursor is TOTAL. Reading past the end of the input yields zeros and an empty slice,
 * never a failure, so every input decodes to some sequence of calls and the end of the input
 * ends the sequence. Nothing here reads a clock, the environment, a file or the network, and
 * nothing allocates except fuzz_dup. */
#ifndef DIGINET_FUZZ_H
#define DIGINET_FUZZ_H

#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "spec.h"

/* The OSS Verify driver refuses an input file this large; the harnesses refuse it too, so
 * the domain they are proven over is the domain they are run over. */
#define FUZZ_INPUT_MAX ((size_t)64 << 20)

/* A property check: a function the sabotage rule can name (fuzz/sabotage.sh finds the
 * innermost check_ function of an abort's stack), so it is never inlined away. */
#define FUZZ_CHECK __attribute__((noinline)) static void

struct fuzz_in {
	const uint8_t *p;
	size_t n;
};

static inline struct fuzz_in fuzz_in(const uint8_t *data, size_t size)
{
	struct fuzz_in in = { data, size };
	return in;
}

static inline uint8_t fuzz_u8(struct fuzz_in *in)
{
	if (in->n == 0)
		return 0;
	in->n--;
	return *in->p++;
}

/* Little-endian, like every multi-byte field the harnesses invent (the wire is big-endian;
 * the harnesses never read the wire with these). */
static inline uint16_t fuzz_u16(struct fuzz_in *in)
{
	uint16_t lo = fuzz_u8(in);
	return (uint16_t)(lo | (uint16_t)fuzz_u8(in) << 8);
}

static inline uint32_t fuzz_u32(struct fuzz_in *in)
{
	uint32_t lo = fuzz_u16(in);
	return lo | (uint32_t)fuzz_u16(in) << 16;
}

/* Up to `want` bytes from the cursor; returns how many there were. */
static inline size_t fuzz_take(struct fuzz_in *in, size_t want, const uint8_t **out)
{
	size_t n = want < in->n ? want : in->n;
	*out = in->p;
	in->p += n;
	in->n -= n;
	return n;
}

/* One length-prefixed record: a u16 LE length, then that many bytes (or what is left). */
static inline size_t fuzz_record(struct fuzz_in *in, const uint8_t **out)
{
	return fuzz_take(in, fuzz_u16(in), out);
}

/* A heap block of exactly `n` bytes (one for n = 0). A frame handed to a parser lives in its
 * own allocation, so a read past its end lands in a redzone the sanitizer watches instead of
 * in the next record of the same input. */
static inline uint8_t *fuzz_alloc(size_t n)
{
	uint8_t *b = malloc(n ? n : 1);
	/* not a property: the harness's own allocation failed */
	if (!b)
		abort();
	return b;
}

static inline uint8_t *fuzz_dup(const uint8_t *p, size_t n)
{
	uint8_t *b = fuzz_alloc(n);
	if (n)
		memcpy(b, p, n);
	return b;
}

/* Whether each of the `n` bytes at `p` is still `fill`: a buffer the library must not write
 * past, filled before the call and read after it. */
static inline int fuzz_all(const uint8_t *p, size_t n, uint8_t fill)
{
	for (size_t i = 0; i < n; i++)
		if (p[i] != fill)
			return 0;
	return 1;
}

#endif /* DIGINET_FUZZ_H */
