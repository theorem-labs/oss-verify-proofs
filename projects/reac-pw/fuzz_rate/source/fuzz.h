// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>

/* What every harness in fuzz/ shares: a cursor over the input, the input-size refusal, and
 * the exact-size copies that let AddressSanitizer see a read one byte past what a reader
 * was given.
 *
 * The cursor is TOTAL. Reading past the end of the input yields zeros and an empty slice,
 * never a failure, so every input decodes to some sequence of calls and the end of the
 * input ends the sequence. Nothing here reads a clock, the environment, a file or the
 * network, and nothing allocates except fuzz_dup and fuzz_str. */
#ifndef REACPW_FUZZ_H
#define REACPW_FUZZ_H

#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* The OSS Verify driver refuses an input file this large; the harnesses refuse it too, so
 * the domain they are proven over is the domain they are run over. */
#define FUZZ_INPUT_MAX ((size_t)64 << 20)

#define FUZZ_NOINLINE __attribute__((noinline))

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

/* Little-endian, like every multi-byte field the harnesses invent. */
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

/* A heap copy of exactly `n` bytes (one byte when `n` is 0, never read). A buffer handed
 * to a reader lives in its own allocation, so a read past its end lands in a redzone the
 * sanitizer watches instead of in the next record of the same input. */
static inline uint8_t *fuzz_dup(const void *p, size_t n)
{
	uint8_t *b = malloc(n ? n : 1);
	/* not a property: the harness's own allocation failed */
	if (!b)
		abort();
	if (n)
		memcpy(b, p, n);
	return b;
}

/* A heap C string of the `n` bytes at p, cut at their first NUL, with its NUL and nothing
 * after it: a reader of text that runs past the terminator reads a redzone. */
static inline char *fuzz_str(const void *p, size_t n)
{
	const uint8_t *z = n ? memchr(p, 0, n) : NULL;
	if (z)
		n = (size_t)(z - (const uint8_t *)p);
	char *s = malloc(n + 1);
	/* not a property: the harness's own allocation failed */
	if (!s)
		abort();
	if (n)
		memcpy(s, p, n);
	s[n] = '\0';
	return s;
}

#endif /* REACPW_FUZZ_H */
