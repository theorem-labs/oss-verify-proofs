// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>

/* libFuzzer harness: THE CONTROLS (src/diginet_codec.c), every encoder diginet_codec.h
 * declares, the personalities, the text helpers of the scribble strip and the counter, and
 * the meter and ring helpers.
 *
 * Input: up to OPS_MAX operations, each [op] and its arguments. op % 15 is the call, and
 * op / 15 % 3 the personality it is given: none (NULL), Control|24, ProControl.
 *    0 u32 strip, u32 value               diginet_fader_encode
 *    1 u32 button, u32 id, u32 on         diginet_button_encode
 *    2 u32 strip, u32 on                  diginet_touch_encode
 *    3 u32 strip, u32 delta               diginet_vpot_encode
 *    4 u32 delta                          diginet_jog_encode
 *    5 u32 strip, u16 mask                diginet_ring_encode
 *    6 u32 channel, u32 right, u32 segs   diginet_meter_encode
 *    7 u32 strip, u32 bits                diginet_strip_leds_encode
 *    8 u32 bits                           diginet_counter_leds_encode
 *    9 u32 addr, c1..c8                   diginet_scribble_encode
 *   10 dots s1..s8                        diginet_counter_encode (s1 the leftmost digit)
 *   11 device fn n p1..pn                 diginet_sysex_encode (n % 25 payload bytes)
 *   12 addr u16-len text                  diginet_scribble_text, then diginet_scribble_encode
 *   13 u16-len text                       diginet_seg7, diginet_counter_text, then
 *                                         diginet_counter_encode
 *   14 u32 n, u16 mask                    diginet_meter_mask, diginet_meter_segments,
 *                                         ring_dot and _fill
 * Each argument is read at the width of its type in diginet_codec.h: an `unsigned` or an `int`
 * as a u32 (an `int` its two's complement), a uint16_t as a u16, every other byte a u8, so an
 * encoder that cuts an argument short before it checks the range shows. The scribble address
 * of op 12 is a u8 & 7f, a valid address, since that op checks the text and not the range;
 * text is cut at its first NUL and at 64 bytes. The text operations use Control|24 when the
 * personality is none.
 *
 * The harness works out what each call owes from docs/protocol.md (the bytes of each
 * control) and from the comments of diginet_codec.h (the range each encoder takes), with the
 * two desks of fuzz/spec.h, and holds the library to that. No expected value comes from the
 * library.
 *
 * Properties, each an abort() in a check_ function:
 *   - personality: each desk is the one docs/protocol.md describes, found by its announce
 *     name, and no other name or desk is one.
 *   - refusal: the system family, function 0x70, is never encoded.
 *   - range: an encoder succeeds exactly for the arguments its comment in diginet_codec.h
 *     takes, fails with the code it gives otherwise, and leaves the command untouched when it
 *     fails.
 *   - bytes: what an encoder makes is the message docs/protocol.md gives for the control, byte
 *     for byte, its key names the address it writes, and only scribble and counter writes are
 *     display writes.
 *   - text: diginet_scribble_text() writes the characters diginet_codec.h:137-140 gives and
 *     reports the bytes it used; diginet_seg7() draws each character with the segments a
 *     seven-segment display lights for it; diginet_counter_text() places digits and dots as
 *     diginet_codec.h:152-158 says; the meter mask and segment count, and the ring dot and
 *     fill, light what they name.
 */
#include <diginet/diginet.h>
#include <diginet/diginet_codec.h>

#include "fuzz.h"

#define OPS_MAX  256
#define TEXT_MAX 64

/* The ranges each encoder takes. contract: include/diginet/diginet_codec.h:74-170 */
#define DATA_MAX   0x7f   /* a MIDI data byte: :117, :136, :160-161 */
#define ID_MAX     0x3f   /* bit 6 of 90 bb (40 | id) is the press: :79 */
#define DELTA_MIN  (-64)  /* dd = delta + 64 is a data byte: :97 */
#define DELTA_MAX  63
#define METER_CH   0x20   /* bit 5 of the channel byte is the side: :112 */

enum { FADER, BUTTON, TOUCH, VPOT, JOG, RING, METER, STRIP_LEDS, COUNTER_LEDS, SCRIBBLE, COUNTER,
       SYSEX, SCRIBBLE_TEXT, COUNTER_TEXT, MASKS };

/* one encoder call: what it was given, what it returned, and what it owed */
struct call {
	int kind;
	const struct diginet_personality *p;
	const struct spec_desk *desk;   /* the desk p should be, or NULL */
	unsigned a, b, c;     /* strip/button/channel/addr, value/id/mask/bits, on/right */
	int delta;
	uint8_t bytes[SPEC_CMD_MAX];    /* scribble chars, counter digits, sysex payload */
	size_t n;
	int rc;
	struct diginet_cmd before, out;
	/* owed */
	int want_rc;
	uint8_t want[SPEC_CMD_MAX];
	size_t want_len;
	uint32_t want_key;
	int want_display;
};

static int seven_bit(const uint8_t *p, size_t n)
{
	for (size_t i = 0; i < n; i++)
		if (p[i] & 0x80)
			return 0;
	return 1;
}

/* F0 13 dd fn payload F7: docs/protocol.md:94-146, protocol/diginet.ksy `sysex` */
static void owe_sysex(struct call *k, uint8_t device, uint8_t fn, const uint8_t *pl, size_t n)
{
	k->want[0] = 0xf0;
	k->want[1] = SPEC_MAKER;
	k->want[2] = device;
	k->want[3] = fn;
	memcpy(k->want + 4, pl, n);
	k->want[4 + n] = 0xf7;
	k->want_len = n + 5;
	k->want_display = fn == SPEC_FN_SCRIBBLE || fn == SPEC_FN_COUNTER;
}

static void owe3(struct call *k, uint8_t a, uint8_t b, uint8_t c, uint32_t key)
{
	k->want[0] = a;
	k->want[1] = b;
	k->want[2] = c;
	k->want_len = 3;
	k->want_key = key;
}

/* What the call owes: the code, and for a success the bytes, the key and the display flag. */
static void owe(struct call *k)
{
	const struct spec_desk *d = k->desk;
	int needs_desk = k->kind != BUTTON && k->kind != JOG && k->kind != SYSEX;

	k->want_rc = SPEC_OK;
	k->want_len = 0;
	k->want_key = 0;
	k->want_display = 0;
	if (needs_desk && !d) {
		k->want_rc = SPEC_E_ARG;
		return;
	}
	switch (k->kind) {
	case FADER:
		/* B0 tt MSB (20+tt) LSB, MSB = v >> 3, LSB = (v & 7) << 4: docs/protocol.md:75 */
		if (k->a >= d->strips || k->b > SPEC_FADER_MAX)
			break;
		k->want[0] = 0xb0;
		k->want[1] = (uint8_t)k->a;
		k->want[2] = (uint8_t)(k->b >> 3);
		k->want[3] = (uint8_t)(0x20 + k->a);
		k->want[4] = (uint8_t)((k->b & 7) << 4);
		k->want_len = 5;
		k->want_key = SPEC_KEY(SPEC_KEY_FADER, k->a);
		return;
	case BUTTON:
		/* 90 bb (40 if on | id): docs/protocol.md:99-100, :111 */
		if (k->a > DATA_MAX || k->b > ID_MAX)
			break;
		owe3(k, 0x90, (uint8_t)k->a, (uint8_t)((k->c ? 0x40 : 0) | k->b),
		     SPEC_KEY(SPEC_KEY_LED, k->a << 8 | k->b));
		return;
	case TOUCH:
		/* 90 09 (40 if touched | tt): docs/protocol.md:79 */
		if (k->a >= d->strips)
			break;
		owe3(k, 0x90, SPEC_BTN_TOUCH, (uint8_t)((k->c ? 0x40 : 0) | k->a), SPEC_KEY(SPEC_KEY_INPUT, 0));
		return;
	case VPOT:
		/* B0 (40 | tt) dd, dd = delta + 64: docs/protocol.md:87 */
		if (k->a >= d->strips || k->delta < DELTA_MIN || k->delta > DELTA_MAX)
			break;
		owe3(k, 0xb0, (uint8_t)(0x40 | k->a), (uint8_t)(k->delta + 64), SPEC_KEY(SPEC_KEY_INPUT, 0));
		return;
	case JOG:
		/* B0 5C dd: docs/protocol.md:89 */
		if (k->delta < DELTA_MIN || k->delta > DELTA_MAX)
			break;
		owe3(k, 0xb0, SPEC_JOG_CC, (uint8_t)(k->delta + 64), SPEC_KEY(SPEC_KEY_INPUT, 0));
		return;
	case RING: {
		/* (tt | 40 if LED 1) b1 b2, b1 bits 6..0 LEDs 2..8, b2 bits 6..0 LEDs 9..15, LED L
		 * bit L - 1 of the mask: docs/protocol.md:94, diginet_codec.h:103 */
		if (k->a >= d->strips || k->b >> SPEC_RING_LEDS)
			break;
		uint8_t pl[3] = { (uint8_t)(k->a | (k->b & 1 ? 0x40 : 0)), 0, 0 };
		for (unsigned led = 2; led <= SPEC_RING_LEDS; led++)
			if (k->b >> (led - 1) & 1)
				pl[led <= 8 ? 1 : 2] |= (uint8_t)(1u << (led <= 8 ? 8 - led : 15 - led));
		owe_sysex(k, d->device, SPEC_FN_RING, pl, 3);
		k->want_key = SPEC_KEY(SPEC_KEY_RING, k->a);
		return;
	}
	case METER: {
		/* ch hi lo, ch | 20 for the right side, n segments the n lowest of 14 bits:
		 * docs/protocol.md:129-130 */
		if (k->a >= METER_CH || k->b > SPEC_METER_BITS)
			break;
		unsigned mask = (1u << k->b) - 1;
		uint8_t ch = (uint8_t)(k->a | (k->c ? 0x20 : 0));
		uint8_t pl[3] = { ch, (uint8_t)(mask >> 7), (uint8_t)(mask & 0x7f) };
		owe_sysex(k, d->device, SPEC_FN_METER, pl, 3);
		k->want_key = SPEC_KEY(SPEC_KEY_METER, ch);
		return;
	}
	case STRIP_LEDS:
	case COUNTER_LEDS: {
		/* tt bits, the counter-mode LEDs at the counter's address: docs/protocol.md:112-113 */
		unsigned addr = k->kind == STRIP_LEDS ? k->a : d->counter;
		if ((k->kind == STRIP_LEDS && k->a >= d->strips) || k->b > DATA_MAX)
			break;
		uint8_t pl[2] = { (uint8_t)addr, (uint8_t)k->b };
		owe_sysex(k, d->device, SPEC_FN_LEDS, pl, 2);
		k->want_key = SPEC_KEY(SPEC_KEY_LEDS, addr);
		return;
	}
	case SCRIBBLE: {
		/* aa 00 c1..cN, N the desk's characters: docs/protocol.md:118, :123 */
		if (k->a > DATA_MAX || !seven_bit(k->bytes, d->chars))
			break;
		uint8_t pl[2 + SPEC_CHARS_MAX] = { (uint8_t)k->a, 0x00 };
		memcpy(pl + 2, k->bytes, d->chars);
		owe_sysex(k, d->device, SPEC_FN_SCRIBBLE, pl, 2u + d->chars);
		k->want_key = SPEC_KEY(SPEC_KEY_SCRIBBLE, k->a);
		return;
	}
	case COUNTER: {
		/* aa dots d8..d1, the rightmost digit first: docs/protocol.md:135 */
		if (k->b > DATA_MAX || !seven_bit(k->bytes, SPEC_DIGITS))
			break;
		uint8_t pl[2 + SPEC_DIGITS] = { d->counter, (uint8_t)k->b };
		for (unsigned i = 0; i < SPEC_DIGITS; i++)
			pl[2 + i] = k->bytes[SPEC_DIGITS - 1 - i];
		owe_sysex(k, d->device, SPEC_FN_COUNTER, pl, sizeof pl);
		k->want_key = SPEC_KEY(SPEC_KEY_COUNTER, d->counter);
		return;
	}
	default:
		/* SYSEX: diginet_codec.h:160-161, the device and function data bytes, the
		 * system family refused, a payload of data bytes that fits a command */
		if (k->a > DATA_MAX) {
			k->want_rc = SPEC_E_ARG;
			return;
		}
		if (k->b == SPEC_FN_SYSTEM) {
			k->want_rc = SPEC_E_REFUSED;
			return;
		}
		if (k->b > DATA_MAX)
			break;
		if (k->n + 5 > SPEC_CMD_MAX) {
			k->want_rc = SPEC_E_SPACE;
			return;
		}
		if (!seven_bit(k->bytes, k->n))
			break;
		owe_sysex(k, (uint8_t)k->a, (uint8_t)k->b, k->bytes, k->n);
		return;
	}
	k->want_rc = SPEC_E_RANGE;
}

FUZZ_CHECK check_personality(void)
{
	const struct diginet_personality *c24 = diginet_personality_of(DIGINET_DESK_CONTROL24);
	const struct diginet_personality *pc = diginet_personality_of(DIGINET_DESK_PROCONTROL);
	/* Each desk is the one docs/protocol.md describes: its announce name, device byte,
	 * strips, scribble characters and counter address.
	 * contract: fuzz/spec.h SPEC_C24, SPEC_PC; docs/protocol.md:47, :73, :118, :123, :135-146
	 * mutant: src/diginet_codec.c:14 `8, 8, 0x09` -> `8, 4, 0x09`
	 * input: encoders-procontrol */
	if (!c24 || !pc || strcmp(c24->announce_name, SPEC_C24.name) || c24->device != SPEC_C24.device ||
	    c24->strips != SPEC_C24.strips || c24->scribble_chars != SPEC_C24.chars ||
	    c24->counter_addr != SPEC_C24.counter || strcmp(pc->announce_name, SPEC_PC.name) ||
	    pc->device != SPEC_PC.device || pc->strips != SPEC_PC.strips ||
	    pc->scribble_chars != SPEC_PC.chars || pc->counter_addr != SPEC_PC.counter ||
	    diginet_personality_of(DIGINET_DESK_UNKNOWN))
		abort();
	/* An announce name selects its desk, and a name no source describes selects none.
	 * contract: diginet_codec.h:40-41; docs/protocol.md:47
	 * mutant: src/diginet_codec.c:22 `!strcmp(name` -> `strcmp(name`
	 * input: encoders-control24 */
	if (diginet_personality_from_name(SPEC_C24.name) != c24 ||
	    diginet_personality_from_name(SPEC_PC.name) != pc ||
	    diginet_personality_from_name("CNTRL|2") || diginet_personality_from_name("MAINUNITS") ||
	    diginet_personality_from_name(""))
		abort();
}

FUZZ_CHECK check_refusal(const struct call *k)
{
	/* The system family, function 0x70, is never encoded.
	 * contract: docs/protocol.md:140-144; diginet_codec.h:160-161
	 * mutant: src/diginet_codec.c:71 `fn == DIGINET_FN_SYSTEM` -> `fn == 0x71`
	 * input: sysex-system */
	if (k->kind == SYSEX && k->b == SPEC_FN_SYSTEM && k->rc == SPEC_OK)
		abort();
}

FUZZ_CHECK check_range(const struct call *k)
{
	/* A failed call leaves the command as it was.
	 * contract: diginet_codec.h:71-72
	 * mutant: src/diginet_codec.c:76 `return DIGINET_E_SPACE;` -> `return out->len = 0, DIGINET_E_SPACE;`
	 * input: out-of-range */
	if (k->rc != SPEC_OK && memcmp(&k->out, &k->before, sizeof k->out))
		abort();
	/* An encoder succeeds exactly for the arguments its comment takes, and otherwise fails
	 * with the code its comment gives.
	 * contract: diginet_codec.h:71-170
	 * mutant: src/diginet_codec.c:100 `strip >= p->strips` -> `strip > p->strips`
	 * input: fader-past-last-strip
	 * mutant: src/diginet_codec.c:100 `strip >= p->strips` -> `(uint8_t)strip >= p->strips`
	 * input: fader-strip-256
	 * mutant: src/diginet_codec.c:138 `delta > 63` -> `delta > 64`
	 * input: out-of-range
	 * mutant: src/diginet_codec.c:184 `mask >> DIGINET_RING_LEDS` -> `mask >> 16`
	 * input: out-of-range */
	if (k->rc != k->want_rc)
		abort();
}

FUZZ_CHECK check_bytes(const struct call *k)
{
	/* What the encoder makes is the control's message, byte for byte.
	 * contract: docs/protocol.md:75-146
	 * mutant: src/diginet_codec.c:106 `<< 4` -> `<< 3`
	 * input: fader-full
	 * mutant: src/diginet_codec.c:193 `0x40 : 0` -> `0x20 : 0`
	 * input: encoders-control24
	 * mutant: src/diginet_codec.c:226 `(uint8_t)(m >> 7)` -> `(uint8_t)(m >> 6)`
	 * input: encoders-control24
	 * mutant: src/diginet_codec.c:381 `seg[DIGINET_COUNTER_DIGITS - 1 - k]` -> `seg[k]`
	 * input: encoders-control24 */
	if (k->out.len != k->want_len || memcmp(k->out.bytes, k->want, k->want_len))
		abort();
	/* Its key names the address it writes, by kind.
	 * contract: diginet_codec.h:48-62
	 * mutant: src/diginet_codec.c:229 `DIGINET_KEY(DIGINET_KEY_METER, ch)` -> `DIGINET_KEY(DIGINET_KEY_METER, channel)`
	 * input: encoders-control24
	 * mutant: include/diginet/diginet_codec.h:61 `<< 16` -> `<< 15`
	 * input: encoders-control24 */
	if (k->out.key != k->want_key)
		abort();
	/* Only scribble and counter writes are display writes, which a transport paces.
	 * contract: diginet_codec.h:67; docs/protocol.md:60
	 * mutant: src/diginet_codec.c:88 `fn == DIGINET_FN_SCRIBBLE || fn == DIGINET_FN_COUNTER` -> `fn == DIGINET_FN_SCRIBBLE`
	 * input: encoders-control24 */
	if (k->out.display != k->want_display)
		abort();
}

/* ---- the text helpers ------------------------------------------------------------------- */

/* The scribble text diginet_codec.h:137-140 gives: ASCII as it is, ".1" to ".9" the dot and
 * small digit glyph chr(digit) - 26 (docs/protocol.md:119), a byte past ASCII '?', spaces up
 * to n; and the number of text bytes used. */
static size_t owed_scribble_text(const char *t, uint8_t *out, size_t n)
{
	size_t i = 0, o = 0;
	while (t[i] && o < n) {
		if (t[i] == '.' && t[i + 1] >= '1' && t[i + 1] <= '9') {
			out[o++] = (uint8_t)(t[i + 1] - 26);
			i += 2;
		} else {
			out[o++] = (unsigned char)t[i] < 0x80 ? (uint8_t)t[i] : '?';
			i++;
		}
	}
	while (o < n)
		out[o++] = ' ';
	return i;
}

/* The segments of each character the counter draws, a..g, bit 6 = a ... bit 0 = g
 * (docs/protocol.md:136): the drawing of each on a seven-segment display. A letter the display
 * draws one way is taken in either case; H and h are the one letter drawn both ways
 * (diginet_codec.h:148-150). */
static int owed_seg7(int c)
{
	static const struct { char c; const char *segs; } GLYPH[] = {
		{ '0', "abcdef" }, { '1', "bc" }, { '2', "abdeg" }, { '3', "abcdg" }, { '4', "bcfg" },
		{ '5', "acdfg" }, { '6', "acdefg" }, { '7', "abc" }, { '8', "abcdefg" }, { '9', "abcdfg" },
		{ 'A', "abcefg" }, { 'b', "cdefg" }, { 'C', "adef" }, { 'd', "bcdeg" }, { 'E', "adefg" },
		{ 'F', "aefg" }, { 'H', "bcefg" }, { 'h', "cefg" }, { 'J', "bcde" }, { 'L', "def" },
		{ 'o', "cdeg" }, { 'P', "abefg" }, { 'r', "eg" }, { 'S', "acdfg" }, { 'U', "bcdef" },
		{ 'Y', "bcdfg" }, { 'Z', "abdeg" }, { '-', "g" }, { ' ', "" },
	};
	for (size_t i = 0; i < sizeof GLYPH / sizeof GLYPH[0]; i++) {
		char g = GLYPH[i].c;
		int same = c == g;
		if (!same && g != 'H' && g != 'h' && ((g >= 'A' && g <= 'Z') || (g >= 'a' && g <= 'z')))
			same = (c | 0x20) == (g | 0x20);
		if (!same)
			continue;
		int v = 0;
		for (const char *s = GLYPH[i].segs; *s; s++)
			v |= 1 << (6 - (*s - 'a'));
		return v;
	}
	return -1;
}

/* The counter text diginet_codec.h:152-158 gives: each character drawn on a digit, a '.' after
 * a character its dot and any other '.' a blank digit with its dot, right-aligned on the 8
 * digits, dots bit k the digit k from the left; refused for a character the display cannot
 * draw, more than 8 digits, or a dot on the rightmost digit, which has no bit
 * (docs/protocol.md:137). */
static int owed_counter_text(const char *t, uint8_t seg[SPEC_DIGITS], uint8_t *dots)
{
	uint8_t s[SPEC_DIGITS];
	int dot[SPEC_DIGITS] = { 0 };
	int n = 0;
	for (; *t; t++) {
		if (*t == '.' && n > 0 && !dot[n - 1]) {
			dot[n - 1] = 1;
			continue;
		}
		int v = owed_seg7(*t == '.' ? ' ' : *t);
		if (v < 0 || n == SPEC_DIGITS)
			return SPEC_E_RANGE;
		dot[n] = *t == '.';
		s[n++] = (uint8_t)v;
	}
	*dots = 0;
	for (int i = 0; i < SPEC_DIGITS; i++) {
		int from = i - (SPEC_DIGITS - n);
		seg[i] = from >= 0 ? s[from] : 0;
		if (from >= 0 && dot[from]) {
			if (i == SPEC_DIGITS - 1)
				return SPEC_E_RANGE;
			*dots |= (uint8_t)(1u << i);
		}
	}
	return SPEC_OK;
}

FUZZ_CHECK check_text_scribble(const char *text, uint8_t *chars, size_t cap, size_t n)
{
	uint8_t want[SPEC_CHARS_MAX];
	size_t used_want = owed_scribble_text(text, want, n);
	/* the whole buffer the call gets, so a write from n on shows */
	memset(chars, 0xa5, cap);
	size_t used = diginet_scribble_text(text, chars, n);
	/* The scribble text is the characters diginet_codec.h:137-140 gives, and the bytes used.
	 * contract: diginet_codec.h:137-140; docs/protocol.md:118-119
	 * mutant: src/diginet_codec.c:275 `text[i + 1] - 26` -> `text[i + 1] - 25`
	 * input: scribble-text
	 * mutant: src/diginet_codec.c:279 `c < 0x80 ? c : '?'` -> `c`
	 * input: scribble-text */
	if (used != used_want || memcmp(chars, want, n))
		abort();
	/* The text is cut at n: no byte from n on is written.
	 * contract: diginet_codec.h:137
	 * mutant: src/diginet_codec.c:282 `o < n` -> `o <= n`
	 * input: scribble-text */
	if (!fuzz_all(chars + n, cap - n, 0xa5))
		abort();
}

FUZZ_CHECK check_text_seg7(void)
{
	int same = 1;
	for (int c = 0; c < 256; c++)
		same &= diginet_seg7((char)c) == owed_seg7((char)c);
	/* Each character is drawn with the segments a seven-segment display lights for it, and a
	 * character the display cannot draw has no pattern.
	 * contract: docs/protocol.md:136; diginet_codec.h:148-151
	 * mutant: src/diginet_codec.c:312 `0x33` -> `0x32`
	 * input: counter-text */
	if (!same)
		abort();
}

FUZZ_CHECK check_text_counter(const char *text, uint8_t *seg, size_t cap, uint8_t *dots)
{
	uint8_t want_seg[SPEC_DIGITS], want_dots = 0;
	int want = owed_counter_text(text, want_seg, &want_dots);
	/* the whole buffer the call gets, so a write past the digits shows */
	memset(seg, 0xa5, cap);
	*dots = 0xa5;
	int r = diginet_counter_text(text, seg, dots);
	/* The counter text is the digits and dots diginet_codec.h:152-158 gives, or refused.
	 * contract: diginet_codec.h:152-158; docs/protocol.md:137
	 * mutant: src/diginet_codec.c:362 `i == DIGINET_COUNTER_DIGITS - 1` -> `i == DIGINET_COUNTER_DIGITS`
	 * input: counter-text-last-dot
	 * mutant: src/diginet_codec.c:345 `!dot[n - 1]` -> `1`
	 * input: counter-text */
	if (r != want || (r == SPEC_OK && (memcmp(seg, want_seg, SPEC_DIGITS) || *dots != want_dots)))
		abort();
	/* The digits are seg[8]: no byte past them is written.
	 * contract: diginet_codec.h:155, seg[DIGINET_COUNTER_DIGITS]
	 * mutant: src/diginet_codec.c:367 `*dots = d;` -> `*dots = d, seg[DIGINET_COUNTER_DIGITS] = 0;`
	 * input: counter-text */
	if (!fuzz_all(seg + SPEC_DIGITS, cap - SPEC_DIGITS, 0xa5))
		abort();
}

FUZZ_CHECK check_text_masks(unsigned n, uint16_t mask)
{
	unsigned lit = n > SPEC_METER_BITS ? SPEC_METER_BITS : n;
	/* The meter mask of n segments is the n lowest bits, at most the 14 a meter has.
	 * contract: docs/protocol.md:130; diginet_codec.h:112-117
	 * mutant: src/diginet_codec.c:205 `segments = DIGINET_METER_SEGMENTS;` -> `segments = 13;`
	 * input: masks */
	if (diginet_meter_mask(n) != (1u << lit) - 1)
		abort();
	/* A mask's segments are its count when it is a thermometer, and -1 when it is not.
	 * contract: diginet_codec.h:118-120; docs/protocol.md:130
	 * mutant: src/diginet_codec.c:214 `(mask >> n) ? -1 : n` -> `n`
	 * input: masks */
	if (diginet_meter_segments(mask) != spec_segments(mask))
		abort();
	/* The ring dot lights LED pos + 1 alone, and nothing past the 15th.
	 * contract: diginet_codec.h:108-109; docs/protocol.md:92
	 * mutant: src/diginet_codec.c:171 `pos < DIGINET_RING_LEDS` -> `pos <= DIGINET_RING_LEDS`
	 * input: masks */
	if (diginet_ring_dot(n) != (n < SPEC_RING_LEDS ? 1u << n : 0))
		abort();
	/* The ring fill lights the first n LEDs, n up to 15, and nothing past.
	 * contract: diginet_codec.h:108-110; docs/protocol.md:92
	 * mutant: src/diginet_codec.c:176 `n <= DIGINET_RING_LEDS` -> `n < DIGINET_RING_LEDS`
	 * input: masks */
	if (diginet_ring_fill(n) != (n <= SPEC_RING_LEDS ? (1u << n) - 1 : 0))
		abort();
}

/* ---- the calls -------------------------------------------------------------------------- */

static void text_arg(struct fuzz_in *in, char *text)
{
	const uint8_t *p;
	size_t n = fuzz_take(in, fuzz_u16(in) % (TEXT_MAX + 1), &p);
	memcpy(text, p, n);
	text[n] = '\0';
}

static void run(struct call *k)
{
	switch (k->kind) {
	case FADER: k->rc = diginet_fader_encode(k->p, k->a, k->b, &k->out); break;
	case BUTTON: k->rc = diginet_button_encode(k->a, k->b, (int)k->c, &k->out); break;
	case TOUCH: k->rc = diginet_touch_encode(k->p, k->a, (int)k->c, &k->out); break;
	case VPOT: k->rc = diginet_vpot_encode(k->p, k->a, k->delta, &k->out); break;
	case JOG: k->rc = diginet_jog_encode(k->delta, &k->out); break;
	case RING: k->rc = diginet_ring_encode(k->p, k->a, (uint16_t)k->b, &k->out); break;
	case METER: k->rc = diginet_meter_encode(k->p, k->a, (int)k->c, k->b, &k->out); break;
	case STRIP_LEDS: k->rc = diginet_strip_leds_encode(k->p, k->a, k->b, &k->out); break;
	case COUNTER_LEDS: k->rc = diginet_counter_leds_encode(k->p, k->b, &k->out); break;
	case SCRIBBLE: k->rc = diginet_scribble_encode(k->p, k->a, k->bytes, &k->out); break;
	case COUNTER: k->rc = diginet_counter_encode(k->p, k->bytes, (uint8_t)k->b, &k->out); break;
	default:
		k->rc = diginet_sysex_encode((uint8_t)k->a, (uint8_t)k->b, k->bytes, k->n, &k->out);
		break;
	}
	owe(k);
	check_refusal(k);
	check_range(k);
	if (k->rc == SPEC_OK)
		check_bytes(k);
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	static const enum diginet_desk DESK[3] = {
		DIGINET_DESK_UNKNOWN, DIGINET_DESK_CONTROL24, DIGINET_DESK_PROCONTROL,
	};
	static const struct spec_desk *const SPEC_DESK[3] = { NULL, &SPEC_C24, &SPEC_PC };
	char text[TEXT_MAX + 1];

	if (size >= FUZZ_INPUT_MAX)
		return 0;
	check_personality();
	struct fuzz_in in = fuzz_in(data, size);
	for (int ops = 0; ops < OPS_MAX && in.n; ops++) {
		uint8_t op = fuzz_u8(&in);
		struct call k;
		const uint8_t *pp;
		memset(&k, 0, sizeof k);
		k.kind = op % 15;
		k.p = diginet_personality_of(DESK[op / 15 % 3]);
		k.desk = SPEC_DESK[op / 15 % 3];
		memset(&k.before, 0xa5, sizeof k.before);
		memcpy(&k.out, &k.before, sizeof k.out);   /* padding too: it is compared */
		switch (k.kind) {
		case FADER:
			k.a = fuzz_u32(&in), k.b = fuzz_u32(&in);
			break;
		case RING:
			k.a = fuzz_u32(&in), k.b = fuzz_u16(&in);
			break;
		case BUTTON:
			k.a = fuzz_u32(&in), k.b = fuzz_u32(&in), k.c = fuzz_u32(&in);
			break;
		case TOUCH:
			k.a = fuzz_u32(&in), k.c = fuzz_u32(&in);
			break;
		case VPOT:
			k.a = fuzz_u32(&in), k.delta = (int32_t)fuzz_u32(&in);
			break;
		case JOG:
			k.delta = (int32_t)fuzz_u32(&in);
			break;
		case METER:
			k.a = fuzz_u32(&in), k.c = fuzz_u32(&in), k.b = fuzz_u32(&in);
			break;
		case STRIP_LEDS:
			k.a = fuzz_u32(&in), k.b = fuzz_u32(&in);
			break;
		case COUNTER_LEDS:
			k.b = fuzz_u32(&in);
			break;
		case SCRIBBLE:
			k.a = fuzz_u32(&in);
			for (int i = 0; i < SPEC_CHARS_MAX; i++)
				k.bytes[i] = fuzz_u8(&in);
			break;
		case COUNTER:
			k.b = fuzz_u8(&in);
			for (int i = 0; i < SPEC_DIGITS; i++)
				k.bytes[i] = fuzz_u8(&in);
			break;
		case SYSEX:
			k.a = fuzz_u8(&in), k.b = fuzz_u8(&in);
			k.n = fuzz_take(&in, fuzz_u8(&in) % (SPEC_CMD_MAX + 1), &pp);
			memcpy(k.bytes, pp, k.n);
			break;
		case SCRIBBLE_TEXT:
			/* the text's characters, then the scribble write that carries them */
			if (!k.p) {
				k.p = diginet_personality_of(DIGINET_DESK_CONTROL24);
				k.desk = &SPEC_C24;
			}
			k.a = fuzz_u8(&in) & 0x7f;
			text_arg(&in, text);
			check_text_scribble(text, k.bytes, sizeof k.bytes, k.desk->chars);
			k.kind = SCRIBBLE;
			break;
		case COUNTER_TEXT: {
			/* the counter text's digits and dots, then the counter write that carries them */
			uint8_t dots;
			if (!k.p) {
				k.p = diginet_personality_of(DIGINET_DESK_CONTROL24);
				k.desk = &SPEC_C24;
			}
			text_arg(&in, text);
			check_text_seg7();
			check_text_counter(text, k.bytes, sizeof k.bytes, &dots);
			/* a text the counter cannot show gives no digits, so no counter write */
			if (owed_counter_text(text, k.bytes, &dots) != SPEC_OK)
				continue;
			k.b = dots;
			k.kind = COUNTER;
			break;
		}
		default: {
			unsigned n = fuzz_u32(&in);
			check_text_masks(n, fuzz_u16(&in));
			continue;
		}
		}
		run(&k);
	}
	return 0;
}
