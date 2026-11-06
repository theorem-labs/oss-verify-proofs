/* SPDX-License-Identifier: GPL-3.0-or-later */
/* Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com> */
/* Modified 2026 by Theorem Labs, PBC: notes when the C library's allocator returns NULL on a request of at most
 * fuzz_alloc_most() bytes (fuzz_alloc_ran_out), and counts a refused request in the peak. */

/* The count of the bytes a reader holds (fuzz/alloc.h). Each block carries its size in a head before the bytes the
 * reader sees; under AddressSanitizer the head is poisoned, so a read just before a block is still a report, and the
 * block still ends where the reader's bytes end. The count is of what the reader asked for, not of the heads. One
 * allocation can be made to fail, as when memory runs out, so a harness reaches what a reader does then. When the C
 * library's allocator itself returns NULL, on an allocation that was not made to fail, memory has run out: that is
 * noted until the next fuzz_alloc_ran_out_reset(). A NULL on a request of more bytes than fuzz_alloc_most() allows is
 * not noted: a correct reader never asks for that much at once, so the harness's checks still judge it. A refused
 * malloc or realloc request counts in the peak, as the bytes the reader asked to hold. */

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "fuzz.h"

#if defined(__has_feature)
#if __has_feature(address_sanitizer)
#include <sanitizer/asan_interface.h>
#define HEAD_HIDE(b) ASAN_POISON_MEMORY_REGION((b), HEAD)
#define HEAD_SHOW(b) ASAN_UNPOISON_MEMORY_REGION((b), HEAD)
#endif
#endif
#ifndef HEAD_HIDE
#define HEAD_HIDE(b) ((void)(b))
#define HEAD_SHOW(b) ((void)(b))
#endif

/* malloc's own alignment, so the reader's bytes are aligned as malloc's would be */
#define HEAD 16u

static size_t g_live, g_peak, g_count, g_fail_at = SIZE_MAX, g_most = SIZE_MAX;
static int g_ran_out;

/* whether this allocation is the one asked to fail; it fails once */
static int failing(void)
{
    if (g_count++ != g_fail_at)
        return 0;
    g_fail_at = SIZE_MAX;
    return 1;
}

static void *own(unsigned char *b, size_t n)
{
    memcpy(b, &n, sizeof(n));
    HEAD_HIDE(b);
    g_live += n;
    if (g_live > g_peak)
        g_peak = g_live;
    return b + HEAD;
}

static size_t disown(unsigned char *b)
{
    size_t n;

    HEAD_SHOW(b);
    memcpy(&n, b, sizeof(n));
    g_live -= n;
    return n;
}

/* the reader asked malloc or realloc for `n` bytes and got NULL from the C library, or none at all for a size the head
 * does not fit beside */
static void refused(size_t n)
{
    const size_t held = n > SIZE_MAX - g_live ? SIZE_MAX : g_live + n;

    if (held > g_peak)
        g_peak = held;
    if (n <= g_most)
        g_ran_out = 1;
}

void *fuzz_malloc(size_t n)
{
    unsigned char *b;

    if (failing())
        return NULL;
    b = n <= SIZE_MAX - HEAD ? malloc(HEAD + n) : NULL;
    if (!b)
    {
        refused(n);
        return NULL;
    }
    return own(b, n);
}

void *fuzz_calloc(size_t k, size_t n)
{
    void *p = k && n > SIZE_MAX / k ? NULL : fuzz_malloc(k * n);

    if (p)
        memset(p, 0, k * n);
    return p;
}

void *fuzz_realloc(void *p, size_t n)
{
    unsigned char *b, *nb;
    size_t old;

    if (!p)
        return fuzz_malloc(n);
    if (failing())
        return NULL;
    if (n > SIZE_MAX - HEAD)
    {
        refused(n);
        return NULL;
    }
    b = (unsigned char *)p - HEAD;
    old = disown(b);
    nb = realloc(b, HEAD + n);
    if (!nb)
    {
        refused(n);
        own(b, old);
        return NULL;
    }
    return own(nb, n);
}

char *fuzz_strdup(const char *s)
{
    const size_t n = strlen(s) + 1;
    char *d = fuzz_malloc(n);

    if (d)
        memcpy(d, s, n);
    return d;
}

void fuzz_free(void *p)
{
    unsigned char *b;

    if (!p)
        return;
    b = (unsigned char *)p - HEAD;
    disown(b);
    free(b);
}

size_t fuzz_alloc_live(void)
{
    return g_live;
}

size_t fuzz_alloc_peak(void)
{
    return g_peak;
}

void fuzz_alloc_peak_reset(void)
{
    g_peak = g_live;
}

size_t fuzz_alloc_count(void)
{
    return g_count;
}

void fuzz_alloc_fail(size_t k)
{
    g_fail_at = k < SIZE_MAX - g_count ? g_count + k : SIZE_MAX;
}

int fuzz_alloc_ran_out(void)
{
    return g_ran_out;
}

void fuzz_alloc_ran_out_reset(void)
{
    g_ran_out = 0;
}

void fuzz_alloc_most(size_t n)
{
    g_most = n;
}
