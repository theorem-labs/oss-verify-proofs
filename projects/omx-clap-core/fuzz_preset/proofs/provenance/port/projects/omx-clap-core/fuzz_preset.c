/* SPDX-License-Identifier: GPL-3.0-or-later */
/* Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com> */
/* Modified 2026 by Theorem Labs, PBC: a call of the fuzz target ends, with no abort, once memory has run out (see
 * "Memory running out" below); a reading that ran out is checked to be refused cleanly first. */

/* fuzz_preset: the preset file reader, pj_parse of src/preset_file.c, over the bytes of a file as pj_read_file hands
 * them to it, and the writer, pj_write, over what it accepts. pj_parse is the one JSON reader of the tree.
 *
 * Input: the file, whole. A file larger than PRESET_FILE_MAX_BYTES is not read, as pj_read_file reads none.
 *
 * Properties, each in a check_ function of its own, `if (!cond) abort();`:
 *   no_overread    the tree is the one the file's own bytes give: the input parsed with a digit after it, with another
 *                  digit after it and with a NUL after it is one answer, and the same tree whenever two of them accept.
 *                  The parse that follows reads the input from a buffer of exactly its size, so a read past it is
 *                  AddressSanitizer's to report.
 *   as_written     the answer is the one the grammar below gives, read by the harness and not by the reader: a file is
 *                  accepted when the grammar reads it, and to the tree the harness reads from it (types, member names
 *                  in order, every string's bytes, every number's text and value).
 *   reject_clean   a refused file leaves the tree as pj_parse found it, every byte zero, and gives back every byte the
 *                  reader took on the way to refusing it. So does the file read again with one of its allocations
 *                  failing (which one, the input's bytes choose), which is refused; and a write with one of the
 *                  writer's failing gives no text and gives its buffer back.
 *   round_trip     an accepted file written back, compact and pretty, is the text the harness renders of the tree in
 *                  the writer's format below, and parses to the same tree; a rewrite that sets one member, as a save
 *                  sets modifiedAt, keeps every other member and its place.
 *   bounded_alloc  for a file of n bytes the reader holds at most PJ_ALLOC_BOUND(n) bytes at once.
 *
 * Memory running out: malloc or realloc returns NULL to the harness, or to the reader on an allocation that
 * fuzz_alloc_fail did not choose (fuzz/alloc.c). A reading during which that happens is refused cleanly (reject_clean),
 * then the call ends and returns 0. A NULL on one request of more than PJ_ALLOC_BOUND(n) bytes, in a call on a file of
 * n bytes, is not memory running out: no correct reader or writer asks for that much at once, so the checks judge it.
 *
 * The grammar, as the reader reads a file: one JSON value (RFC 8259) and whitespace around it, with three differences.
 * Arrays and objects nest JSON_DEPTH_MAX (32) deep at most. A string holds no \u0000, and a \u escape of a surrogate
 * is a pair, high then low. A number is an optional '-' and a digit, a 0 not followed by another digit, then the
 * longest run of digits, '.', 'e', 'E', '+' and '-', which strtod reads whole to a finite value: "1." and "1.e5" are
 * numbers. A number's text is that run, its value what strtod reads.
 *
 * The writer's format: compact, no whitespace; pretty, each item on a line of its own indented two spaces for each
 * level, ": " after a member name, the closing bracket on a line of its own under its opener unless the container is
 * empty, and a newline at the end. A string escapes '"' and '\\' with a backslash, a newline, tab and carriage return as
 * \n, \t and \r, and every other byte under 0x20 as \u00xx in lower case; a number is written as its text.
 */

#include <math.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "fuzz.h"
#include "preset_file.h"

/* How deep the grammar lets arrays and objects nest: the 32 of fuzz/README.md, the harness's own and not the reader's
 * PRESET_JSON_DEPTH_MAX, so that a reader whose limit moves refuses or reads what the grammar does not. */
#define JSON_DEPTH_MAX 32

/* An item costs its container at most two slots (the slots double), and the first item eight; each slot is a struct pj
 * and, in an object, a key pointer. A container that is closed and followed by another item takes at least four bytes
 * of file; arrays nested deep around one digit, repeated, cost about 220 bytes of tree for each. The containers still
 * open take one byte each, and there are JSON_DEPTH_MAX of them at most: their first eight slots are the
 * constant. */
#define PJ_SLOT (sizeof(struct pj) + sizeof(char *))
#define PJ_ALLOC_BOUND(n) (256u * (size_t)(n) + JSON_DEPTH_MAX * 8u * PJ_SLOT + 4096u)

/* the member a save rewrites */
#define REWRITTEN "modifiedAt"

/* fuzz/alloc.c: whether memory has run out since the last fuzz_alloc_ran_out_reset(): the C library's allocator
 * returned NULL on one of the reader's allocations that fuzz_alloc_fail did not choose, of at most fuzz_alloc_most(n)'s
 * n bytes (SIZE_MAX until it is called) */
int fuzz_alloc_ran_out(void);
void fuzz_alloc_ran_out_reset(void);
void fuzz_alloc_most(size_t n);

/* whether one of the harness's own allocations returned NULL in this call of the fuzz target */
static int g_own_ran_out;

/* whether memory has run out in this call, for the reader or for the harness: the call then ends */
static int out_of_memory(void)
{
    return g_own_ran_out || fuzz_alloc_ran_out();
}

/* one of the harness's own allocations, a NULL noted as memory running out */
static void *noted(void *p)
{
    if (!p)
        g_own_ran_out = 1;
    return p;
}

static int same(const struct pj *a, const struct pj *b)
{
    size_t i;

    if (a->type != b->type || a->n != b->n)
        return 0;
    switch (a->type)
    {
    case PJ_NUMBER:
        return strcmp(a->str, b->str) == 0 && memcmp(&a->num, &b->num, sizeof(a->num)) == 0;
    case PJ_STRING:
        return strcmp(a->str, b->str) == 0;
    case PJ_ARRAY:
    case PJ_OBJECT:
        for (i = 0; i < a->n; i++)
            if ((a->type == PJ_OBJECT && strcmp(a->keys[i], b->keys[i]) != 0) || !same(&a->kids[i], &b->kids[i]))
                return 0;
        return 1;
    default:
        return 1;
    }
}

/* ---------------------------------------------------------------- the grammar, read by the harness */

struct ex
{
    const char *p, *end;
    int depth;
    char *scratch;      // a string's or a number's bytes, room for the whole file
    int differs;        // the tree compared with is not the one read
};

static int ex_digit(char c)
{
    return c >= '0' && c <= '9';
}

static void ex_ws(struct ex *in)
{
    while (in->p < in->end && (*in->p == ' ' || *in->p == '\t' || *in->p == '\n' || *in->p == '\r'))
        in->p++;
}

static int ex_hex4(const char *p, unsigned *out)
{
    unsigned v = 0;
    int i;

    for (i = 0; i < 4; i++)
    {
        const char c = p[i];
        const int d = ex_digit(c) ? c - '0'
                    : c >= 'a' && c <= 'f' ? c - 'a' + 10
                    : c >= 'A' && c <= 'F' ? c - 'A' + 10
                    : -1;

        if (d < 0)
            return -1;
        v = v * 16 + (unsigned)d;
    }
    *out = v;
    return 0;
}

/* a code point as UTF-8 (RFC 3629) */
static size_t ex_utf8(unsigned char *o, unsigned cp)
{
    if (cp < 0x80)
    {
        o[0] = (unsigned char)cp;
        return 1;
    }
    if (cp < 0x800)
    {
        o[0] = (unsigned char)(0xC0 | cp >> 6);
        o[1] = (unsigned char)(0x80 | (cp & 0x3F));
        return 2;
    }
    if (cp < 0x10000)
    {
        o[0] = (unsigned char)(0xE0 | cp >> 12);
        o[1] = (unsigned char)(0x80 | (cp >> 6 & 0x3F));
        o[2] = (unsigned char)(0x80 | (cp & 0x3F));
        return 3;
    }
    o[0] = (unsigned char)(0xF0 | cp >> 18);
    o[1] = (unsigned char)(0x80 | (cp >> 12 & 0x3F));
    o[2] = (unsigned char)(0x80 | (cp >> 6 & 0x3F));
    o[3] = (unsigned char)(0x80 | (cp & 0x3F));
    return 4;
}

/* a string at in->p, its opening quote, into in->scratch: 0, or -1 when the grammar refuses it. No escape is longer
 * than what it stands for, so the scratch holds any string of the file. */
static int ex_string(struct ex *in)
{
    const char *p = in->p + 1;
    unsigned char *o = (unsigned char *)in->scratch;

    while (p < in->end && *p != '"')
    {
        const unsigned char c = (unsigned char)*p++;
        unsigned cp, lo;

        if (c < 0x20)
            return -1;
        if (c != '\\')
        {
            *o++ = c;
            continue;
        }
        if (p >= in->end)
            return -1;
        switch (*p++)
        {
        case '"': *o++ = '"'; break;
        case '\\': *o++ = '\\'; break;
        case '/': *o++ = '/'; break;
        case 'b': *o++ = 0x08; break;
        case 'f': *o++ = 0x0C; break;
        case 'n': *o++ = 0x0A; break;
        case 'r': *o++ = 0x0D; break;
        case 't': *o++ = 0x09; break;
        case 'u':
            if (in->end - p < 4 || ex_hex4(p, &cp) != 0 || cp == 0 || (cp >= 0xDC00 && cp <= 0xDFFF))
                return -1;
            p += 4;
            if (cp >= 0xD800 && cp <= 0xDBFF)
            {
                if (in->end - p < 6 || p[0] != '\\' || p[1] != 'u' || ex_hex4(p + 2, &lo) != 0 || lo < 0xDC00
                    || lo > 0xDFFF)
                    return -1;
                p += 6;
                cp = 0x10000 + (cp - 0xD800) * 0x400 + (lo - 0xDC00);
            }
            o += ex_utf8(o, cp);
            break;
        default:
            return -1;
        }
    }
    if (p >= in->end)
        return -1;
    *o = '\0';
    in->p = p + 1;
    return 0;
}

static int ex_value(struct ex *in, const struct pj *v);

static int ex_number(struct ex *in, const struct pj *v)
{
    const char *s = in->p;
    char *end;
    double num;

    if (*s == '-')
        s++;
    if (s >= in->end || !ex_digit(*s) || (*s == '0' && s + 1 < in->end && ex_digit(s[1])))
        return -1;
    while (s < in->end && (ex_digit(*s) || *s == '.' || *s == 'e' || *s == 'E' || *s == '+' || *s == '-'))
        s++;
    memcpy(in->scratch, in->p, (size_t)(s - in->p));
    in->scratch[s - in->p] = '\0';
    num = strtod(in->scratch, &end);
    if (*end != '\0' || !isfinite(num))
        return -1;
    if (v && (v->type != PJ_NUMBER || strcmp(v->str, in->scratch) != 0 || memcmp(&v->num, &num, sizeof(num)) != 0))
        in->differs = 1;
    in->p = s;
    return 0;
}

static int ex_items(struct ex *in, const struct pj *v)
{
    const int object = *in->p == '{';
    const char close = object ? '}' : ']';
    size_t n = 0;

    if (++in->depth > JSON_DEPTH_MAX)
        return -1;
    if (v && v->type != (object ? PJ_OBJECT : PJ_ARRAY))
    {
        in->differs = 1;
        v = NULL;
    }
    in->p++;
    ex_ws(in);
    if (in->p < in->end && *in->p == close)
        in->p++;
    else
        for (;; n++)
        {
            const struct pj *kid = v && n < v->n ? &v->kids[n] : NULL;

            if (v && !kid)
                in->differs = 1;
            if (object)
            {
                ex_ws(in);
                if (in->p >= in->end || *in->p != '"' || ex_string(in) != 0)
                    return -1;
                if (kid && strcmp(v->keys[n], in->scratch) != 0)
                    in->differs = 1;
                ex_ws(in);
                if (in->p >= in->end || *in->p != ':')
                    return -1;
                in->p++;
            }
            if (ex_value(in, kid) != 0)
                return -1;
            ex_ws(in);
            if (in->p < in->end && *in->p == ',')
            {
                in->p++;
                continue;
            }
            if (in->p >= in->end || *in->p != close)
                return -1;
            in->p++;
            n++;
            break;
        }
    if (v && n != v->n)
        in->differs = 1;
    in->depth--;
    return 0;
}

static int ex_word(struct ex *in, const char *word, enum pj_type type, const struct pj *v)
{
    const size_t len = strlen(word);

    if ((size_t)(in->end - in->p) < len || memcmp(in->p, word, len) != 0)
        return -1;
    if (v && v->type != type)
        in->differs = 1;
    in->p += len;
    return 0;
}

/* the value at in->p: 0, or -1 when the grammar refuses it; in->differs set when it is not `v` (NULL: no tree) */
static int ex_value(struct ex *in, const struct pj *v)
{
    ex_ws(in);
    if (in->p >= in->end)
        return -1;
    switch (*in->p)
    {
    case '{':
    case '[':
        return ex_items(in, v);
    case '"':
        if (ex_string(in) != 0)
            return -1;
        if (v && (v->type != PJ_STRING || strcmp(v->str, in->scratch) != 0))
            in->differs = 1;
        return 0;
    case 't': return ex_word(in, "true", PJ_TRUE, v);
    case 'f': return ex_word(in, "false", PJ_FALSE, v);
    case 'n': return ex_word(in, "null", PJ_NULL, v);
    default: return ex_number(in, v);
    }
}

/* What the grammar reads in `size` bytes of `text`: -1 when it refuses them; 0 when it reads `doc` (NULL: no tree to
 * compare), 1 when it reads another tree. -1 too when memory ran out for its scratch (out_of_memory then says so). */
static int expected(const char *text, size_t size, const struct pj *doc)
{
    struct ex in = { text, text + size, 0, noted(malloc(size + 1)), 0 };
    int rc;

    if (!in.scratch)
        return -1;
    rc = ex_value(&in, doc);
    if (rc == 0)
    {
        ex_ws(&in);
        rc = in.p == in.end ? 0 : -1;
    }
    free(in.scratch);
    return rc != 0 ? -1 : in.differs;
}

/* ---------------------------------------------------------------- the writer's format, rendered by the harness */

struct text
{
    char *b;
    size_t n, cap;
    int failed;         // memory ran out: the text is cut, and no more is added
};

static void tx_put(struct text *t, const char *s, size_t n)
{
    char *b;

    if (t->failed)
        return;
    if (t->n + n + 1 > t->cap)
    {
        b = noted(realloc(t->b, (t->n + n + 1) * 2));
        if (!b)
        {
            t->failed = 1;
            return;
        }
        t->b = b;
        t->cap = (t->n + n + 1) * 2;
    }
    memcpy(t->b + t->n, s, n);
    t->n += n;
    t->b[t->n] = '\0';
}

static void tx_string(struct text *t, const char *s)
{
    static const char hex[] = "0123456789abcdef";

    tx_put(t, "\"", 1);
    for (; *s; s++)
    {
        const unsigned char c = (unsigned char)*s;
        const char esc[6] = { '\\', c == 0x0A ? 'n' : c == 0x09 ? 't' : c == 0x0D ? 'r' : 'u', '0', '0', hex[c >> 4],
                              hex[c & 15] };

        if (c == '"' || c == '\\')
        {
            tx_put(t, "\\", 1);
            tx_put(t, s, 1);
        }
        else if (c >= 0x20)
            tx_put(t, s, 1);
        else
            tx_put(t, esc, esc[1] == 'u' ? 6 : 2);
    }
    tx_put(t, "\"", 1);
}

static void tx_line(struct text *t, int depth)
{
    int i;

    tx_put(t, "\n", 1);
    for (i = 0; i < depth; i++)
        tx_put(t, "  ", 2);
}

static void tx_value(struct text *t, const struct pj *v, int pretty, int depth)
{
    size_t i;

    switch (v->type)
    {
    case PJ_NULL: tx_put(t, "null", 4); break;
    case PJ_FALSE: tx_put(t, "false", 5); break;
    case PJ_TRUE: tx_put(t, "true", 4); break;
    case PJ_NUMBER: tx_put(t, v->str, strlen(v->str)); break;
    case PJ_STRING: tx_string(t, v->str); break;
    case PJ_ARRAY:
    case PJ_OBJECT:
        tx_put(t, v->type == PJ_OBJECT ? "{" : "[", 1);
        for (i = 0; i < v->n; i++)
        {
            if (i)
                tx_put(t, ",", 1);
            if (pretty)
                tx_line(t, depth + 1);
            if (v->type == PJ_OBJECT)
            {
                tx_string(t, v->keys[i]);
                tx_put(t, ":", 1);
                if (pretty)
                    tx_put(t, " ", 1);
            }
            tx_value(t, &v->kids[i], pretty, depth + 1);
        }
        if (pretty && v->n)
            tx_line(t, depth);
        tx_put(t, v->type == PJ_OBJECT ? "}" : "]", 1);
        break;
    }
}

/* the text of `doc` in the writer's format, malloc'd; NULL when memory ran out */
static char *rendered(const struct pj *doc, int pretty)
{
    struct text t = { NULL, 0, 0, 0 };

    tx_put(&t, "", 0);
    tx_value(&t, doc, pretty, 0);
    if (pretty)
        tx_put(&t, "\n", 1);
    if (t.failed)
    {
        free(t.b);
        return NULL;
    }
    return t.b;
}

/* ---------------------------------------------------------------- the properties */

static __attribute__((noinline)) void check_reject_clean(int rc, const struct pj *doc, size_t live_before);

/* pj_parse of `text`; a reading during which memory ran out is refused cleanly */
static int parse_noting(const char *text, size_t size, struct pj *doc)
{
    const size_t live = fuzz_alloc_live();
    const int rc = pj_parse(text, size, doc);

    if (fuzz_alloc_ran_out())
        check_reject_clean(rc, doc, live);
    return rc;
}

/* fuzz_copy's padded copy of the input (fuzz.h), but NULL when memory runs out */
static char *padded(const uint8_t *data, size_t size, char fill)
{
    char *b = noted(malloc(size + FUZZ_PAD));

    if (b)
    {
        if (size)
            memcpy(b, data, size);
        memset(b + size, fill, FUZZ_PAD);
    }
    return b;
}

/* 1 when memory ran out, and the call ends */
static __attribute__((noinline)) int check_no_overread(const uint8_t *data, size_t size)
{
    static const struct pj empty;
    char *one = padded(data, size, '1'), *two = padded(data, size, '2'), *nul = padded(data, size, '\0');
    struct pj a1 = empty, a2 = empty, a0 = empty;
    int r1 = -1, r2 = -1, r0 = -1, ran_out;

    if (!out_of_memory())
        r1 = parse_noting(one, size, &a1);
    if (!out_of_memory())
        r2 = parse_noting(two, size, &a2);
    if (!out_of_memory())
        r0 = parse_noting(nul, size, &a0);
    ran_out = out_of_memory();
    if (!ran_out)
    {
        /* The same tree, whatever follows the file: a number that runs on into the bytes past it reads differently
         * after a 1 and after a 2.
         * mutant: src/preset_file.c:298 `text + len,` -> `text + len + 1,`
         * input: number-alone */
        if (r1 == 0 && ((r2 == 0 && !same(&a1, &a2)) || (r0 == 0 && !same(&a1, &a0))))
            abort();
        /* One answer, whatever follows the file.
         * mutant: src/preset_file.c:193 `s + 1 < in->end` -> `s + 1 <= in->end`
         * input: zero-alone */
        if (r1 != r0 || r2 != r0)
            abort();
    }
    pj_free(&a1);
    pj_free(&a2);
    pj_free(&a0);
    free(one);
    free(two);
    free(nul);
    return ran_out;
}

static __attribute__((noinline)) void check_bounded_alloc(size_t held, size_t size)
{
    /* mutant: src/preset_file.c:50 `: 8;` -> `: 512;`
     * input: many-small-containers */
    if (held > PJ_ALLOC_BOUND(size))
        abort();
}

/* 1 when memory ran out for the harness's own reading, and the call ends */
static __attribute__((noinline)) int check_as_written(const uint8_t *data, size_t size, int rc, const struct pj *doc)
{
    const int want = expected((const char *)data, size, rc == 0 ? doc : NULL);

    if (out_of_memory())
        return 1;
    /* The reader refuses a file the grammar reads, or reads one it refuses.
     * mutant: src/preset_file.c:155 `cp == 0` -> `cp == 1`
     * input: refuse-u0000
     * mutant: src/preset_file.h:63 `32` -> `31`
     * input: deepest */
    if ((rc == 0) != (want >= 0))
        abort();
    /* The tree is the one the file spells. A reader that reads an escape wrong and a writer that writes it back the
     * same way make a round trip that holds; the harness's own reading does not.
     * mutant: src/preset_file.c:151 `'\n'` -> `'\r'`
     * input: escapes */
    if (rc == 0 && want != 0)
        abort();
    return 0;
}

static __attribute__((noinline)) void check_reject_clean(int rc, const struct pj *doc, size_t live_before)
{
    static const struct pj empty;

    /* A reading that loses an allocation is refused: one that takes another instead reads on.
     * mutant: src/preset_file.c:127 `out = malloc((size_t)(o - p) + 1);` -> `out = malloc((size_t)(o - p) + 1) ?: malloc((size_t)(o - p) + 1);`
     * input: string-alone */
    if (rc == 0)
        abort();
    /* mutant: src/preset_file.c:307 `pj_free(out);` -> ``
     * input: refuse-array-cut */
    if (memcmp(doc, &empty, sizeof(empty)) != 0)
        abort();
    /* mutant: src/preset_file.c:246 `v->n++;` -> ``
     * input: refuse-array-cut */
    if (fuzz_alloc_live() != live_before)
        abort();
}

/* The file again with one of the allocations its reading took failing, as when memory runs out: refused like any
 * refusal. And a tree written, pretty and compact, with one of the writer's failing: no text, and its buffer given
 * back. A reading or a write during which memory ran out as well ends the call. */
static __attribute__((noinline)) void check_reject_clean_starved(const uint8_t *data, size_t size, size_t took,
                                                                 const struct pj *doc)
{
    struct pj starved;
    size_t live = fuzz_alloc_live(), before;
    char *text;
    int rc;

    if (took)
    {
        fuzz_alloc_fail(fuzz_pick(data, size, took));
        rc = pj_parse((const char *)data, size, &starved);
        fuzz_alloc_fail(SIZE_MAX);
        check_reject_clean(rc, &starved, live);
    }
    if (!doc || out_of_memory())
        return;
    before = fuzz_alloc_count();
    fuzz_free(pj_write(doc, 1));
    if (fuzz_alloc_count() == before || out_of_memory())
        return;
    fuzz_alloc_fail(fuzz_pick(data, size, fuzz_alloc_count() - before));
    text = pj_write(doc, 1);
    fuzz_alloc_fail(SIZE_MAX);
    if (out_of_memory())
    {
        fuzz_free(text);
        return;
    }
    /* mutant: src/preset_file.c:465 `buf = realloc(o->buf, cap);` -> `buf = realloc(o->buf, cap) ?: realloc(o->buf, cap);`
     * input: string-alone */
    if (text || fuzz_alloc_live() != live)
        abort();
    /* The same of a compact write. A text of 4096 bytes or more takes a second allocation, and when that one fails the
     * first still holds the text up to where it failed: a cut text, not none. */
    before = fuzz_alloc_count();
    fuzz_free(pj_write(doc, 0));
    if (fuzz_alloc_count() == before || out_of_memory())
        return;
    fuzz_alloc_fail(fuzz_pick(data, size, fuzz_alloc_count() - before));
    text = pj_write(doc, 0);
    fuzz_alloc_fail(SIZE_MAX);
    if (out_of_memory())
    {
        fuzz_free(text);
        return;
    }
    /* mutant: src/preset_file.c:565 `if (o.failed)` -> `if (o.failed && pretty)`
     * input: compact-second-allocation */
    if (text || fuzz_alloc_live() != live)
        abort();
}

/* written in the writer's format, and read back to the same tree; the compact reading is handed back in `copy`. 1 when
 * memory ran out, and the call ends. */
static int round_trip_text(const struct pj *doc, int pretty, struct pj *copy)
{
    char *text = pj_write(doc, pretty), *want = rendered(doc, pretty);
    struct pj back;
    int rc;

    if (out_of_memory())
    {
        free(want);
        fuzz_free(text);
        return 1;
    }
    /* A tree is written while memory lasts.
     * mutant: src/preset_file.c:565 `if (o.failed)` -> `if (!o.failed)`
     * input: string-alone */
    if (!text)
        abort();
    /* The text is the writer's format, byte for byte.
     * mutant: src/preset_file.c:522 `put(o, "  ", 2);` -> `put(o, "   ", 3);`
     * input: no-modified-at */
    if (strcmp(text, want) != 0)
        abort();
    rc = parse_noting(text, strlen(text), &back);
    free(want);
    fuzz_free(text);
    if (out_of_memory())
        return 1;
    /* The reader reads what the writer writes: a pretty text has the newlines a compact file need not.
     * mutant: src/preset_file.c:38 `*in->p == '\n'` -> `*in->p == '\v'`
     * input: string-alone */
    if (rc != 0)
        abort();
    /* And reads it to the same tree: an escape the writer uses that the file did not.
     * mutant: src/preset_file.c:153 `'\t'` -> `'x'`
     * input: escape-tab-as-u */
    if (!same(doc, &back))
        abort();
    if (copy)
        *copy = back;
    else
        pj_free(&back);
    return 0;
}

/* a save's rewrite of an object: REWRITTEN set, in place when the file has it (its first), appended when not. 1 when
 * memory ran out, and the call ends. */
static int round_trip_rewrite(const struct pj *doc, struct pj *copy)
{
    char *saved;
    struct pj back, v;
    size_t i, at = doc->n;
    int set, rc;

    set = pj_string(&v, "2026-10-25T00:00:00Z") == 0 && pj_set(copy, REWRITTEN, &v) == 0;
    if (out_of_memory())
        return 1;
    /* A member is set while memory lasts.
     * mutant: src/preset_file.c:384 `grow(obj) != 0` -> `grow(obj) == 0`
     * input: no-modified-at */
    if (!set)
        abort();
    saved = pj_write(copy, 1);
    rc = saved && !out_of_memory() ? parse_noting(saved, strlen(saved), &back) : -1;
    if (out_of_memory())
    {
        fuzz_free(saved);
        return 1;
    }
    /* The rewrite is written and read back: a file of no strings has written none until the save adds one.
     * mutant: src/preset_file.c:511 `put(o, "\"", 1);` -> ``
     * input: empty-object */
    if (!saved || rc != 0)
        abort();
    for (i = 0; i < doc->n && at == doc->n; i++)
        if (strcmp(doc->keys[i], REWRITTEN) == 0)
            at = i;
    /* A member the file has is set in place, not added again.
     * mutant: src/preset_file.c:377 `if (old)` -> `if (0)`
     * input: docs-presets-example */
    if (back.n != doc->n + (at == doc->n ? 1u : 0u))
        abort();
    for (i = 0; i < doc->n; i++)
        /* Every other member keeps its name, its value and its place.
         * mutant: src/preset_file.c:380 `*old = *val;` -> `obj->kids[0] = *val;`
         * input: docs-presets-example */
        if (strcmp(back.keys[i], doc->keys[i]) != 0 || (i != at && !same(&back.kids[i], &doc->kids[i])))
            abort();
    /* The member set is the one named, with its value.
     * mutant: src/preset_file.c:384 `strdup(key)` -> `strdup("x")`
     * input: no-modified-at */
    if (strcmp(back.keys[at], REWRITTEN) != 0 || back.kids[at].type != PJ_STRING)
        abort();
    /* The member set holds the value that the rewrite set.
     * mutant: src/preset_file.c:380 `*old = *val;` -> `old->type = val->type;`
     * input: docs-presets-example */
    if (strcmp(back.kids[at].str, "2026-10-25T00:00:00Z") != 0)
        abort();
    fuzz_free(saved);
    pj_free(&back);
    return 0;
}

/* 1 when memory ran out, and the call ends */
static __attribute__((noinline)) int check_round_trip(const struct pj *doc)
{
    static const struct pj empty;
    struct pj copy = empty;
    const int ran_out = round_trip_text(doc, 0, &copy) || round_trip_text(doc, 1, NULL)
                        || (doc->type == PJ_OBJECT && round_trip_rewrite(doc, &copy));

    pj_free(&copy);
    return ran_out;
}

/* the members docs/presets.md names, looked up as a consumer looks them up; what they say is not this reader's */
static void read_members(const struct pj *doc)
{
    static const char *const top[] = { "format", "id", "name", "carries", "createdAt", REWRITTEN };
    const struct pj *params = pj_get(doc, "params"), *state = pj_get(doc, "state");
    volatile size_t seen = 0;
    size_t i;

    for (i = 0; i < sizeof(top) / sizeof(top[0]); i++)
        seen += pj_get_str(doc, top[i]) != NULL;
    seen += pj_get_str(pj_get(doc, "plugin"), "id") != NULL;
    for (i = 0; params && params->type == PJ_ARRAY && i < params->n; i++)
        seen += pj_get_str(&params->kids[i], "symbol") != NULL && pj_get(&params->kids[i], "value") != NULL;
    seen += pj_get_str(state, "encoding") != NULL && pj_get_str(state, "bytes") != NULL;
    (void)seen;
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
    struct pj doc;
    size_t live, count;
    int rc;

    if (size > PRESET_FILE_MAX_BYTES)
        return 0;
    g_own_ran_out = 0;
    fuzz_alloc_ran_out_reset();
    fuzz_alloc_most(PJ_ALLOC_BOUND(size));
    if (check_no_overread(data, size))
        return 0;

    live = fuzz_alloc_live();
    count = fuzz_alloc_count();
    fuzz_alloc_peak_reset();
    rc = parse_noting((const char *)data, size, &doc);
    check_bounded_alloc(fuzz_alloc_peak() - live, size);
    count = fuzz_alloc_count() - count;
    if (out_of_memory() || check_as_written(data, size, rc, &doc))
    {
        pj_free(&doc);
        return 0;
    }
    if (rc != 0)
    {
        check_reject_clean(rc, &doc, live);
        check_reject_clean_starved(data, size, count, NULL);
        return 0;
    }
    read_members(&doc);
    if (!check_round_trip(&doc))
        check_reject_clean_starved(data, size, count, &doc);
    pj_free(&doc);
    return 0;
}
