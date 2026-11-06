/* SPDX-License-Identifier: GPL-3.0-or-later */
/*
 * This file is part of plugin-hostd.
 *
 * plugin-hostd is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * plugin-hostd is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with plugin-hostd.  If not, see <http://www.gnu.org/licenses/>.
 *
 * Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>
 */

/* What the two libFuzzer harnesses share: a cursor over the input, the input-size refusal, and the exact-size copy
 * that lets the sanitizer see a read one byte past a message.
 *
 * The cursor is total. Reading past the end of the input yields zeros and an empty slice, never a failure, so every
 * input decodes to some sequence of calls and the end of the input ends it. Nothing here reads a clock, the
 * environment, a file or the network. */

#ifndef PLUGIN_HOSTD_FUZZ_H
#define PLUGIN_HOSTD_FUZZ_H

#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* the OSS Verify driver refuses an input this large; the harnesses refuse it too, so the domain they are proven over
 * is the domain they are run over */
#define FUZZ_INPUT_MAX ((size_t)64 << 20)

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

/* little-endian, like every multi-byte field the harnesses invent */
static inline uint16_t fuzz_u16(struct fuzz_in *in)
{
    uint16_t lo = fuzz_u8(in);

    return (uint16_t)(lo | (uint16_t)fuzz_u8(in) << 8);
}

/* up to `want` bytes from the cursor; returns how many there were */
static inline size_t fuzz_take(struct fuzz_in *in, size_t want, const uint8_t **out)
{
    size_t n = want < in->n ? want : in->n;

    *out = in->p;
    in->p += n;
    in->n -= n;
    return n;
}

/* a heap copy of exactly `n` bytes, with no terminator: a message handed to the daemon lives in its own allocation, so
 * a read past its end lands in a redzone the sanitizer watches */
static inline char *fuzz_dup(const uint8_t *p, size_t n)
{
    char *b = malloc(n ? n : 1);

    /* not a property: the harness got no memory for its copy of the message */
    if (b == NULL)
        abort();
    if (n)
        memcpy(b, p, n);
    return b;
}

#endif
