/* SPDX-License-Identifier: GPL-3.0-or-later */
/* Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com> */

/* fuzz_state: the plugin state body of a preset file, preset_base64_decode of src/preset_file.c over the text of
 * state.bytes, and the body on its way back to a file: preset_base64_encode, and the body through a whole preset
 * document (pj_write, pj_parse, pj_get_str). The host parses no other state body: one saved to a state file is handed to
 * the plugin as its bytes (clap_state_load in src/effects.c, through the core's bounded istream), and the LV2 adapter's
 * body is Turtle that lilv reads; the plugin and lilv are not the target here.
 *
 * Input: the text, up to its first NUL; a string the preset reader accepts holds none. A text larger than
 * PRESET_FILE_MAX_BYTES is no member of a file the reader reads.
 *
 * Properties, each in a check_ function of its own, `if (!cond) abort();`:
 *   no_overread    the body is the one the text gives: the text with two letters of the alphabet after its NUL ("AA"
 *                  and "BA", which a decoder that reads them decodes, and which its buffer always has room for) and
 *                  with a NUL there decodes to one answer, and to the same bytes whenever two of them decode. The decode that follows reads a copy of exactly the text and
 *                  its NUL, so a read past it is AddressSanitizer's to report.
 *   as_written     the answer is the one the grammar below gives, read by the harness and not by the decoder: the text
 *                  is refused when the grammar refuses it, and decodes to the bytes the harness reads from it when not.
 *   reject_clean   a refused text gives back every byte the decoder took and leaves the length it was handed unwritten;
 *                  so does any text decoded with its allocation failing, which is refused, and a body encoded with the
 *                  encoder's failing gives no text.
 *   round_trip     a body encoded is the text the harness encodes of it, (len + 2) / 3 * 4 characters, and decodes to
 *                  the same bytes; a text that is already that encoding is what the body encodes to; set as
 *                  state.bytes of a preset written and read back, the body decodes to the same bytes.
 *   bounded_alloc  for a text of n characters the decoder holds at most n / 4 * 3 + 3 bytes.
 *
 * The grammar, as the decoder reads a text: RFC 4648 base64. A space, tab, CR or LF anywhere is skipped. Each character
 * of the alphabet gives six bits, and each group of four of them three bytes; a last group of two gives one byte and of
 * three two, and the bits of it past those bytes are zero; a last group of one is refused. '=' may follow the last of
 * them, twice at most, and nothing but '=' and whitespace after it: padding is allowed, not required.
 */

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "fuzz.h"
#include "preset_file.h"

#define B64_ALLOC_BOUND(n) ((size_t)(n) / 4u * 3u + 3u)

static int same_body(const uint8_t *a, size_t an, const uint8_t *b, size_t bn)
{
    return an == bn && (an == 0 || memcmp(a, b, an) == 0);
}

/* the six bits a character of RFC 4648's alphabet stands for, -1 for a character outside it */
static int b64_value(char c)
{
    if (c >= 'A' && c <= 'Z')
        return c - 'A';
    if (c >= 'a' && c <= 'z')
        return c - 'a' + 26;
    if (c >= '0' && c <= '9')
        return c - '0' + 52;
    return c == '+' ? 62 : c == '/' ? 63 : -1;
}

static char b64_char(unsigned v)
{
    return v < 26 ? (char)('A' + v) : v < 52 ? (char)('a' + v - 26) : v < 62 ? (char)('0' + v - 52)
         : v == 62 ? '+' : '/';
}

/* The text read by the grammar of the header: the bytes it gives into `out` (B64_ALLOC_BOUND of its length), and how
 * many; SIZE_MAX when the grammar refuses it. */
static size_t expected_body(const char *text, uint8_t *out)
{
    const size_t len = strlen(text);
    uint8_t *six = malloc(len ? len : 1);
    size_t m = 0, i, n = 0, r;
    int pad = 0;

    /* not a property: the harness's own allocation failed */
    if (!six)
        abort();
    for (; *text; text++)
    {
        const int v = b64_value(*text);

        if (*text == ' ' || *text == '\t' || *text == '\r' || *text == '\n')
            continue;
        if (*text == '=')
            pad++;
        else if (v < 0 || pad)
            break;
        else
            six[m++] = (uint8_t)v;
    }
    r = m % 4;
    if (*text || pad > 2 || r == 1 || (r == 2 && (six[m - 1] & 15) != 0) || (r == 3 && (six[m - 1] & 3) != 0))
        n = SIZE_MAX;
    for (i = 0; n != SIZE_MAX && i < m; i += 4)
    {
        out[n++] = (uint8_t)(six[i] << 2 | six[i + 1] >> 4);
        if (i + 2 < m)
            out[n++] = (uint8_t)((six[i + 1] & 15) << 4 | six[i + 2] >> 2);
        if (i + 3 < m)
            out[n++] = (uint8_t)((six[i + 2] & 3) << 6 | six[i + 3]);
    }
    free(six);
    return n;
}

/* the padded encoding of RFC 4648 of `len` bytes, into `out` of (len + 2) / 3 * 4 + 1 */
static void expected_text(const uint8_t *body, size_t len, char *out)
{
    size_t i;

    for (i = 0; i < len; i += 3)
    {
        const unsigned b0 = body[i], b1 = i + 1 < len ? body[i + 1] : 0, b2 = i + 2 < len ? body[i + 2] : 0;

        *out++ = b64_char(b0 >> 2);
        *out++ = b64_char((b0 & 3) << 4 | b1 >> 4);
        *out++ = i + 1 < len ? b64_char((b1 & 15) << 2 | b2 >> 6) : '=';
        *out++ = i + 2 < len ? b64_char(b2 & 63) : '=';
    }
    *out = '\0';
}

/* the text, its NUL, then `c` and 'A', then NULs */
static char *past_nul(const uint8_t *data, size_t n, char c)
{
    char *b = fuzz_copy(data, n, 1, FUZZ_PAD, '\0');

    b[n + 1] = c;
    b[n + 2] = 'A';
    return b;
}

static __attribute__((noinline)) void check_no_overread(const uint8_t *data, size_t n)
{
    char *ca = past_nul(data, n, 'A'), *cb = past_nul(data, n, 'B'), *cz = fuzz_copy(data, n, 1, FUZZ_PAD, '\0');
    size_t la = 0, lb = 0, lz = 0;
    uint8_t *a = preset_base64_decode(ca, &la), *b = preset_base64_decode(cb, &lb), *z = preset_base64_decode(cz, &lz);

    /* One answer, whatever follows the NUL.
     * mutant: src/preset_file.c:620 `continue;` -> `{ text++; continue; }`
     * input: rfc4648-f-newline */
    if (!a != !z || !b != !z)
        abort();
    /* The same bytes, whatever follows the NUL.
     * mutant: src/preset_file.c:620 `continue;` -> `{ text++; continue; }`
     * input: trailing-newline */
    if (z && (!same_body(a, la, z, lz) || !same_body(b, lb, z, lz)))
        abort();
    fuzz_free(a);
    fuzz_free(b);
    fuzz_free(z);
    free(ca);
    free(cb);
    free(cz);
}

static __attribute__((noinline)) void check_bounded_alloc(size_t held, size_t n)
{
    /* mutant: src/preset_file.c:608 `strlen(text) / 4 * 3 + 3` -> `strlen(text) * 3 + 3`
     * input: rfc4648-f */
    if (held > B64_ALLOC_BOUND(n))
        abort();
}

static __attribute__((noinline)) void check_as_written(const char *text, const uint8_t *body, size_t len)
{
    uint8_t *want = malloc(B64_ALLOC_BOUND(strlen(text)));
    size_t n;

    /* not a property: the harness's own allocation failed */
    if (!want)
        abort();
    n = expected_body(text, want);
    /* The decoder refuses a text the grammar reads, or reads one it refuses.
     * mutant: src/preset_file.c:638 `pad > 2` -> `pad > 3`
     * input: refuse-three-pads */
    if (!body != (n == SIZE_MAX))
        abort();
    /* The bytes are the ones the text spells, not the ones the decoder's own table gives: a letter the encoder and the
     * decoder both read wrong is a round trip that holds.
     * mutant: src/preset_file.c:575 `"ABCDEF` -> `"BACDEF`
     * input: bytes-0-255 */
    if (body && !same_body(body, len, want, n))
        abort();
    free(want);
}

static __attribute__((noinline)) void check_reject_clean(const uint8_t *body, size_t len, size_t live_before)
{
    /* mutant: src/preset_file.c:608 `malloc(strlen(text) / 4 * 3 + 3);` -> `malloc(strlen(text) / 4 * 3 + 3) ?: malloc(strlen(text) / 4 * 3 + 3);`
     * input: rfc4648-f */
    if (body)
        abort();
    /* mutant: src/preset_file.c:643 `free(out);` -> `free(out), *len = n;`
     * input: refuse-letter */
    if (len != SIZE_MAX)
        abort();
    /* mutant: src/preset_file.c:643 `free(out);` -> ``
     * input: refuse-letter */
    if (fuzz_alloc_live() != live_before)
        abort();
}

/* the text decoded again with its allocation failing, as when memory runs out: refused like any refusal; and the body
 * encoded with the encoder's failing: no text, nothing held */
static __attribute__((noinline)) void check_reject_clean_starved(const char *text, const uint8_t *body, size_t len)
{
    const size_t live = fuzz_alloc_live();
    size_t n = SIZE_MAX;
    uint8_t *starved;
    char *encoded;

    fuzz_alloc_fail(0);
    starved = preset_base64_decode(text, &n);
    fuzz_alloc_fail(SIZE_MAX);
    check_reject_clean(starved, n, live);
    if (!body)
        return;
    fuzz_alloc_fail(0);
    encoded = preset_base64_encode(body, len);
    fuzz_alloc_fail(SIZE_MAX);
    /* mutant: src/preset_file.c:579 `malloc((len + 2) / 3 * 4 + 1)` -> `malloc((len + 2) / 3 * 4 + 1) ?: malloc((len + 2) / 3 * 4 + 1)`
     * input: rfc4648-f */
    if (encoded || fuzz_alloc_live() != live)
        abort();
}

/* the body as state.bytes of a preset document, written and read back */
static void round_trip_document(const char *text, const uint8_t *body, size_t len)
{
    struct pj doc, state, v, back;
    const char *bytes;
    char *file;
    uint8_t *got;
    size_t n = 0;

    pj_object(&doc);
    pj_object(&state);
    /* A member is set while memory lasts.
     * mutant: src/preset_file.c:384 `grow(obj) != 0` -> `grow(obj) == 0`
     * input: rfc4648-f */
    if (pj_string(&v, PRESET_FORMAT_STATE) != 0 || pj_set(&doc, "format", &v) != 0
        || pj_string(&v, PRESET_CARRIES_STATE) != 0 || pj_set(&doc, "carries", &v) != 0
        || pj_string(&v, PRESET_ENCODING_BASE64) != 0 || pj_set(&state, "encoding", &v) != 0
        || pj_string(&v, PRESET_CONTEXT_PRESET) != 0 || pj_set(&state, "context", &v) != 0
        || pj_string(&v, text) != 0 || pj_set(&state, "bytes", &v) != 0 || pj_set(&doc, "state", &state) != 0)
        abort();
    file = pj_write(&doc, 1);
    /* The document is written and read back.
     * mutant: src/preset_file.c:511 `put(o, "\"", 1);` -> ``
     * input: rfc4648-f */
    if (!file || pj_parse(file, strlen(file), &back) != 0)
        abort();
    bytes = pj_get_str(pj_get(&back, "state"), "bytes");
    /* And its state.bytes decode to the body.
     * mutant: src/preset_file.c:368 `? v->str :` -> `? v->str + 1 :`
     * input: rfc4648-foobar */
    if (!bytes || !(got = preset_base64_decode(bytes, &n)) || !same_body(got, n, body, len))
        abort();
    fuzz_free(got);
    fuzz_free(file);
    pj_free(&back);
    pj_free(&doc);
}

/* `text` without its whitespace, when it is the padded encoding's length: what the body must encode to */
static int canonical(const char *text, char *out)
{
    size_t n = 0;

    for (; *text; text++)
        if (*text != ' ' && *text != '\t' && *text != '\r' && *text != '\n')
            out[n++] = *text;
    out[n] = '\0';
    return n % 4 == 0;
}

static __attribute__((noinline)) void check_round_trip(const char *input, const uint8_t *body, size_t len)
{
    char *text = preset_base64_encode(body, len), *want = malloc((len + 2) / 3 * 4 + 1);
    char *same = malloc(strlen(input) + 1);
    uint8_t *back;
    size_t n = 0;

    /* not a property: the harness's own allocation failed */
    if (!want || !same)
        abort();
    expected_text(body, len, want);
    /* mutant: src/preset_file.c:600 `*o++ = '=';` -> ``
     * input: rfc4648-f */
    if (!text || strlen(text) != (len + 2) / 3 * 4)
        abort();
    /* A text that is already the body's encoding is what the encoder writes of it.
     * mutant: src/preset_file.c:599 `i + 1 < len ? g_b64[(w >> 6) & 63] : '='` -> `g_b64[(w >> 6) & 63]`
     * input: rfc4648-f */
    if (canonical(input, same) && strcmp(text, same) != 0)
        abort();
    /* The encoder writes the body's encoding, letter for letter.
     * mutant: src/preset_file.c:599 `i + 1 < len ? g_b64[(w >> 6) & 63] : '='` -> `g_b64[(w >> 6) & 63]`
     * input: unpadded-f */
    if (strcmp(text, want) != 0)
        abort();
    back = preset_base64_decode(text, &n);
    /* The encoding decodes to the body: a padded text the decoder must read, where the input was not padded.
     * mutant: src/preset_file.c:621 `*text == '='` -> `*text == '=' && 0`
     * input: unpadded-f */
    if (!back || !same_body(back, n, body, len))
        abort();
    round_trip_document(text, body, len);
    fuzz_free(back);
    fuzz_free(text);
    free(want);
    free(same);
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
    const size_t n = fuzz_strnlen(data, size);
    char *text;
    uint8_t *body;
    size_t len = SIZE_MAX, live;

    if (n > PRESET_FILE_MAX_BYTES)
        return 0;
    check_no_overread(data, n);

    text = fuzz_copy(data, n, 1, 0, 0);
    live = fuzz_alloc_live();
    fuzz_alloc_peak_reset();
    body = preset_base64_decode(text, &len);
    check_bounded_alloc(fuzz_alloc_peak() - live, n);
    check_as_written(text, body, len);
    if (!body)
        check_reject_clean(body, len, live);
    else
        check_round_trip(text, body, len);
    check_reject_clean_starved(text, body, len);
    fuzz_free(body);
    free(text);
    return 0;
}
