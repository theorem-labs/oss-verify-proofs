/* Copyright 2026 Theorem Labs, PBC
 * SPDX-License-Identifier: Apache-2.0
 *
 * fuzz_preset_oom: a test of fuzz_preset.c and alloc.c of this directory, not a fuzz target that is published. For one
 * input it makes the C library's malloc or realloc return NULL at each allocation, in turn, that one call of
 * fuzz_preset makes (the harness's own and, through alloc.c, the reader's), and requires that call to return 0 with no
 * abort each time: memory running out anywhere ends the call as a refusal does.
 *
 * Built in the project image, as build.sh builds fuzz_preset, with each object's references renamed by objcopy:
 *
 *     fuzz_preset.o: malloc, realloc -> oom_malloc, oom_realloc; pj_parse, pj_write, pj_set, pj_string ->
 *                    oom_pj_parse, ...; LLVMFuzzerTestOneInput -> preset_one_input
 *     alloc.o:       malloc, realloc -> oom_malloc, oom_realloc
 *     $CC $CFLAGS fuzz_preset_oom.o fuzz_preset.o alloc.o -o fuzz_preset_oom $LIB_FUZZING_ENGINE \
 *         libomx-clap-readers.a -lm
 *
 * Run as the fuzz target is, `fuzz_preset_oom <input file>` (the driver's six-byte header, then the preset file). It
 * counts the allocations a call makes (N), then for k = 0 .. N-1 forks a child whose k-th allocation fails. It writes
 * one line per k to fd 2:
 *
 *     k <k> <malloc|realloc> size <n> caller <address> in <entry>#<i> from <address> status <wait status>
 *
 * where caller is the address the failed allocation returns to (in the harness, or in alloc.c for the reader), entry
 * the reader or writer function running then (pj_parse, pj_write, pj_set, pj_string, or - for the harness's own work),
 * i its ordinal in the call, and from the harness address that called it. The test fails (abort) when any child does
 * not exit with status 0. */
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

#include "preset_file.h"

int preset_one_input(const uint8_t *data, size_t size);

static size_t g_calls, g_fail_at = SIZE_MAX;
static const char *g_entry = "-";
static unsigned g_ordinal;
static void *g_entry_from;
static unsigned g_entries;

static void note(const char *what, size_t n, void *caller)
{
    char line[256];
    int len = snprintf(line, sizeof(line), "%s size %zu caller %p in %s#%u from %p", what, n, caller, g_entry,
                       g_ordinal, g_entry_from);

    if (len > 0)
        (void)!write(3, line, (size_t)len < sizeof(line) ? (size_t)len : sizeof(line) - 1);
}

__attribute__((noinline)) void *oom_malloc(size_t n)
{
    if (g_calls++ == g_fail_at)
    {
        note("malloc", n, __builtin_return_address(0));
        return NULL;
    }
    return malloc(n);
}

__attribute__((noinline)) void *oom_realloc(void *p, size_t n)
{
    if (g_calls++ == g_fail_at)
    {
        note("realloc", n, __builtin_return_address(0));
        return NULL;
    }
    return realloc(p, n);
}

#define ENTRY(name) (g_entry = #name, g_ordinal = ++g_entries, g_entry_from = __builtin_return_address(0))

__attribute__((noinline)) int oom_pj_parse(const char *text, size_t len, struct pj *out)
{
    int rc;

    ENTRY(pj_parse);
    rc = pj_parse(text, len, out);
    g_entry = "-";
    return rc;
}

__attribute__((noinline)) char *oom_pj_write(const struct pj *v, int pretty)
{
    char *text;

    ENTRY(pj_write);
    text = pj_write(v, pretty);
    g_entry = "-";
    return text;
}

__attribute__((noinline)) int oom_pj_set(struct pj *obj, const char *key, struct pj *val)
{
    int rc;

    ENTRY(pj_set);
    rc = pj_set(obj, key, val);
    g_entry = "-";
    return rc;
}

__attribute__((noinline)) int oom_pj_string(struct pj *v, const char *s)
{
    int rc;

    ENTRY(pj_string);
    rc = pj_string(v, s);
    g_entry = "-";
    return rc;
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
    size_t n, k, bad = 0;
    int fds[2];

    g_calls = 0;
    g_fail_at = SIZE_MAX;
    if (preset_one_input(data, size) != 0)
        abort();
    n = g_calls;
    dprintf(2, "allocations %zu\n", n);
    for (k = 0; k < n; k++)
    {
        char what[256];
        ssize_t got;
        pid_t pid;
        int status;

        if (pipe(fds) != 0)
            abort();
        pid = fork();
        if (pid < 0)
            abort();
        if (pid == 0)
        {
            close(fds[0]);
            if (dup2(fds[1], 3) < 0)
                _exit(99);
            g_calls = 0;
            g_fail_at = k;
            g_entries = 0;
            _exit(preset_one_input(data, size) == 0 ? 0 : 98);
        }
        close(fds[1]);
        got = read(fds[0], what, sizeof(what) - 1);
        close(fds[0]);
        what[got > 0 ? got : 0] = '\0';
        if (waitpid(pid, &status, 0) != pid)
            abort();
        dprintf(2, "k %zu %s status %d\n", k, got > 0 ? what : "(no allocation failed)", status);
        bad += status != 0;
    }
    dprintf(2, "children %zu, not clean %zu\n", n, bad);
    if (bad)
        abort();
    return 0;
}
