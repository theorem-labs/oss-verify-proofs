/* SPDX-License-Identifier: GPL-3.0-or-later */
/* Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com> */

/* fuzz_manifest: the one Turtle reader of the tree that reads the bytes itself, lv2_locate_manifest_names of
 * src/lv2_locate.c, over the text of a bundle's manifest.ttl and the plugin URI it is asked for. Every other ttl the
 * host and the LV2 adapter read goes through lilv (lv2/core/lv2_world.c), which is not the target here.
 *
 * Input: one byte k, then k bytes of URI, then the manifest; each read as C strings are, up to a first NUL. A manifest
 * larger than lv2_locate's 4 MiB is not read.
 *
 * Properties, each in a check_ function of its own, `if (!cond) abort();`:
 *   no_overread    the answer is the one the text and the URI give: both with a name character after their NUL and
 *                  with a NUL there answer the same. The call that follows reads copies of exactly each string and its
 *                  NUL, so a read past them is AddressSanitizer's to report.
 *   as_written     the answer is the one the rule below gives, read by the harness and not by the reader: a manifest
 *                  the rule says names the URI is a candidate, and one it says does not is not.
 *   reject_clean   no answer, a refusal ("does not name it") above all, leaves a byte of the reader's held; asked with
 *                  its allocation failing, it holds nothing either.
 *   round_trip     the URI written as a manifest reads back as one that names it: as "<uri>", and at every split into a
 *                  namespace and a plain local name as "@prefix p: <ns> . p:local", "PREFIX p: <ns> p:local" and
 *                  "@prefix : <ns> . :local"; the empty text names nothing; and the same spellings with one more name
 *                  character after the URI's end answer what the rule says of them.
 *   bounded_alloc  the reader holds at most the URI's length and three bytes.
 *
 * The rule, as src/lv2_locate.h states it: a manifest names a URI that is not empty when it holds "<uri>", or declares a
 * namespace ns the URI starts with, by "@prefix p: <ns>" or by a SPARQL "PREFIX p: <ns>" (any case, at the start of the
 * text or after whitespace), whose rest is a plain local name (letters, digits, '_', '-', ':' and '.', not last), and
 * holds p:local as a whole token: not after a name character or '.', not before a name character. A name character is
 * one a Turtle prefixed name continues with: a letter, a digit, '_', '-', ':', '%', '\\' or a byte from 0x80. The first
 * '>' after "<" ends a namespace, the next declaration is looked for after it, and a "<" with no '>' after it ends the
 * reading. A manifest with more than PREFIXES_MAX (16) declarations of such a namespace is a candidate unread.
 */

#include <ctype.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "fuzz.h"
#include "lv2_locate.h"

/* MANIFEST_MAX_BYTES of src/lv2_locate.c: read_manifest reads no larger file */
#define MANIFEST_MAX ((size_t)4 << 20)

#define NAMES_ALLOC_BOUND(uri_len) ((size_t)(uri_len) + 3u)

/* How many declarations of a namespace the URI starts with a manifest is read for: the 16 of fuzz/README.md, the
 * harness's own and not the reader's LV2_LOCATE_PREFIXES_MAX, so that a reader whose limit moves names what the rule
 * does not. */
#define PREFIXES_MAX 16

/* ---------------------------------------------------------------- the rule, read by the harness */

static int ex_space(char c)
{
    return c == ' ' || c == '\t' || c == '\n' || c == '\v' || c == '\f' || c == '\r';
}

static int ex_alnum(char c)
{
    return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9');
}

static int ex_name_char(char c)
{
    return ex_alnum(c) || c == '_' || c == '-' || c == ':' || c == '%' || c == '\\' || (unsigned char)c >= 0x80;
}

/* what a prefixed name may spell unescaped: letters, digits, '_', '-', ':' and '.', not last */
static int plain(const char *s)
{
    size_t n = strlen(s), i;

    if (n == 0 || s[n - 1] == '.')
        return 0;
    for (i = 0; i < n; i++)
        if (!ex_alnum(s[i]) && s[i] != '_' && s[i] != '-' && s[i] != '.' && s[i] != ':')
            return 0;
    return 1;
}

/* the six letters of "prefix" at `p`, in any case */
static int ex_prefix_word(const char *p)
{
    static const char word[] = "prefix";
    int i;

    for (i = 0; i < 6; i++)
        if (p[i] != word[i] && p[i] != word[i] - 'a' + 'A')
            return 0;
    return 1;
}

/* whether `text` holds prefix:local as a whole token */
static int ex_token(const char *text, const char *prefix, size_t prefix_len, const char *local)
{
    const size_t local_len = strlen(local), len = strlen(text);
    size_t i;

    for (i = 0; i + prefix_len + 1 + local_len <= len; i++)
    {
        const char *s = text + i;

        if (memcmp(s, prefix, prefix_len) != 0 || s[prefix_len] != ':'
            || memcmp(s + prefix_len + 1, local, local_len) != 0)
            continue;
        if ((i > 0 && (ex_name_char(s[-1]) || s[-1] == '.')) || ex_name_char(s[prefix_len + 1 + local_len]))
            continue;
        return 1;
    }
    return 0;
}

/* whether `text` holds "<uri>" */
static int ex_whole(const char *text, const char *uri, size_t n)
{
    for (; (text = strchr(text, '<')) != NULL; text++)
        if (strncmp(text + 1, uri, n) == 0 && text[1 + n] == '>')
            return 1;
    return 0;
}

/* what the rule says of `text` and `uri`: 1 when the manifest names it, else 0 */
static int expected(const char *text, const char *uri)
{
    const size_t n = strlen(uri);
    size_t i, declared = 0;

    if (n == 0)
        return 0;
    if (ex_whole(text, uri, n))
        return 1;
    for (i = 0; text[i]; i++)
    {
        const char *p = text + i, *name, *ns, *close;
        size_t name_len, ns_len;

        if (p[0] == '@' && strncmp(p + 1, "prefix", 6) == 0)
            p += 7;
        else if (ex_prefix_word(p) && (i == 0 || ex_space(p[-1])))
            p += 6;
        else
            continue;
        if (!ex_space(*p))
            continue;
        while (ex_space(*p))
            p++;
        for (name = p; *p && *p != ':' && !ex_space(*p); p++)
            ;
        if (*p != ':')
            continue;
        name_len = (size_t)(p - name);
        for (p++; ex_space(*p); p++)
            ;
        if (*p != '<')
            continue;
        ns = p + 1;
        if (!(close = strchr(ns, '>')))
            return 0;
        ns_len = (size_t)(close - ns);
        if (ns_len < n && strncmp(uri, ns, ns_len) == 0 && plain(uri + ns_len))
        {
            if (++declared > PREFIXES_MAX)
                return 1;
            if (ex_token(text, name, name_len, uri + ns_len))
                return 1;
        }
        i = (size_t)(close - text);
    }
    return 0;
}

/* ---------------------------------------------------------------- the properties */

static __attribute__((noinline)) void check_no_overread(const uint8_t *uri, size_t un, const uint8_t *text, size_t tn)
{
    char *ua = fuzz_copy(uri, un, 1, FUZZ_PAD, 'a'), *ta = fuzz_copy(text, tn, 1, FUZZ_PAD, 'a');
    char *ub = fuzz_copy(uri, un, 1, FUZZ_PAD, '\0'), *tb = fuzz_copy(text, tn, 1, FUZZ_PAD, '\0');

    /* mutant: src/lv2_locate.c:71 `at[local_len]` -> `at[local_len + 1]`
     * input: name-at-end */
    if (lv2_locate_manifest_names(ta, ua) != lv2_locate_manifest_names(tb, ub))
        abort();
    free(ua);
    free(ta);
    free(ub);
    free(tb);
}

static __attribute__((noinline)) void check_bounded_alloc(size_t held, size_t uri_len)
{
    /* mutant: src/lv2_locate.c:94 `malloc(uri_len + 3)` -> `malloc(uri_len * 2 + 3)`
     * input: whole */
    if (held > NAMES_ALLOC_BOUND(uri_len))
        abort();
}

static __attribute__((noinline)) void check_as_written(const char *text, const char *uri, int named)
{
    const int want = expected(text, uri);

    /* A manifest that names the URI is a candidate.
     * mutant: src/lv2_locate.c:98 `found = strstr(text, whole) != NULL;` -> `found = 0;`
     * input: whole */
    if (want && !named)
        abort();
    /* A manifest that does not name it is not: "ex:gain2" is not "ex:gain".
     * mutant: src/lv2_locate.c:71 `name_char(at[local_len])` -> `0`
     * input: longer-local
     * mutant: src/lv2_locate.h:43 `16` -> `15`
     * input: prefixes-most-read */
    if (named && !want)
        abort();
}

static __attribute__((noinline)) void check_reject_clean(size_t live_before)
{
    /* mutant: src/lv2_locate.c:99 `free(whole);` -> ``
     * input: whole */
    if (fuzz_alloc_live() != live_before)
        abort();
}

/* asked again with the reader's allocation failing, as when memory runs out: whatever it answers, it holds nothing */
static __attribute__((noinline)) void check_reject_clean_starved(const char *text, const char *uri)
{
    const size_t live = fuzz_alloc_live();

    fuzz_alloc_fail(0);
    (void)lv2_locate_manifest_names(text, uri);
    fuzz_alloc_fail(SIZE_MAX);
    check_reject_clean(live);
}

static void must_name(const char *text, const char *uri)
{
    /* mutant: src/lv2_locate.c:112 `p = at + 6;` -> `p = at + 7;`
     * input: whole */
    if (lv2_locate_manifest_names(text, uri) != 1)
        abort();
}

static void as_ruled(const char *text, const char *uri)
{
    /* One more name character after the URI's end is another name, and what the reader answers is the rule's.
     * mutant: src/lv2_locate.c:71 `name_char(at[local_len])` -> `0`
     * input: whole */
    if (lv2_locate_manifest_names(text, uri) != expected(text, uri))
        abort();
}

static __attribute__((noinline)) void check_round_trip(const char *uri)
{
    const size_t n = strlen(uri), size = 3 * n + 64;
    char *text;
    size_t k;

    /* The empty text names nothing.
     * mutant: src/lv2_locate.c:147 `return 0;` -> `return 1;`
     * input: whole */
    if (lv2_locate_manifest_names("", uri) != 0)
        abort();
    if (n == 0)
        return;
    text = malloc(size);
    /* not a property: the harness's own allocation failed */
    if (!text)
        abort();
    snprintf(text, size, "<%s>\n    a lv2:Plugin .\n", uri);
    must_name(text, uri);
    snprintf(text, size, "<%sX>\n    a lv2:Plugin .\n", uri);
    as_ruled(text, uri);
    // a namespace is an IRI: no '>' inside it
    for (k = 1; k < n && uri[k - 1] != '>'; k++)
    {
        const char *local = uri + k;

        if (!plain(local))
            continue;
        snprintf(text, size, "@prefix p: <%.*s> .\np:%s\n    a lv2:Plugin .\n", (int)k, uri, local);
        must_name(text, uri);
        snprintf(text, size, "PREFIX p: <%.*s>\np:%s\n    a lv2:Plugin .\n", (int)k, uri, local);
        must_name(text, uri);
        snprintf(text, size, "@prefix : <%.*s> .\n:%s\n    a lv2:Plugin .\n", (int)k, uri, local);
        must_name(text, uri);
        snprintf(text, size, "@prefix p: <%.*s> .\np:%sX\n    a lv2:Plugin .\n", (int)k, uri, local);
        as_ruled(text, uri);
    }
    free(text);
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
    const size_t k = size ? (data[0] < size - 1 ? data[0] : size - 1) : 0;
    const uint8_t *uri = data + (size ? 1 : 0), *text = uri + k;
    const size_t un = fuzz_strnlen(uri, k), tn = fuzz_strnlen(text, size - (size ? 1 : 0) - k);
    char *u, *t;
    size_t live;
    int named;

    if (tn > MANIFEST_MAX)
        return 0;
    check_no_overread(uri, un, text, tn);

    u = fuzz_copy(uri, un, 1, 0, 0);
    t = fuzz_copy(text, tn, 1, 0, 0);
    live = fuzz_alloc_live();
    fuzz_alloc_peak_reset();
    named = lv2_locate_manifest_names(t, u);
    check_bounded_alloc(fuzz_alloc_peak() - live, un);
    check_as_written(t, u, named);
    check_reject_clean(live);
    check_reject_clean_starved(t, u);
    check_round_trip(u);
    free(u);
    free(t);
    return 0;
}
