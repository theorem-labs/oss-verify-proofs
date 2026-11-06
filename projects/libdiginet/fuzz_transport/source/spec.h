// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>

/* THE PROTOCOL AS THE HARNESSES HOLD IT. Every expected value a check of fuzz/ compares with
 * the library comes from here or from the input, never from include/diginet/ or from a
 * library function: a check whose answer came from the code it judges holds for a library
 * that is wrong the same way. Each value is written from protocol/diginet.ksy and
 * docs/protocol.md, and names the line it stands on (its `contract:`); the few that only the
 * library's header defines (its return codes, the key of a command, a size the API promises)
 * are written out here too, so a change to the header is a change a check sees.
 *
 * The readers below are the harnesses' own reading of the grammar: a frame (diginet.ksy, the
 * top-level seq and `header`), the command stream (`commands`, `message`, `sysex`) and the
 * controls in it (docs/protocol.md, "The command set"). They are written for clarity, not
 * speed, and share no code with src/. Nothing here reads a clock, the environment or a file,
 * and nothing here allocates or aborts. */
#ifndef DIGINET_FUZZ_SPEC_H
#define DIGINET_FUZZ_SPEC_H

#include <stddef.h>
#include <stdint.h>
#include <string.h>

/* ---- the frame -------------------------------------------------------------------------- */

/* contract: protocol/diginet.ksy seq `ethertype` (valid: 0x885f); docs/protocol.md:26 */
#define SPEC_ETHERTYPE   0x885f
/* contract: protocol/diginet.ksy seq `dst`, `src` (size: 6 each), `ethertype` (u2) */
#define SPEC_MAC         6
#define SPEC_ETH_HDR     14
/* contract: protocol/diginet.ksy `header`: u2 + u2 + u4 + u4 + u2 + u1 + u1 */
#define SPEC_HDR         16
#define SPEC_BODY_AT     (SPEC_ETH_HDR + SPEC_HDR)
/* contract: docs/protocol.md:30, a body padded to the Ethernet minimum, a 46-byte payload */
#define SPEC_MIN_FRAME   (SPEC_ETH_HDR + 46)
/* contract: Ethernet II carries at most a 1500-byte payload (FCS excluded), the largest frame
 * diginet.h:111-114 says diginet_frame_build() makes */
#define SPEC_MAX_FRAME   (SPEC_ETH_HDR + 1500)
#define SPEC_MAX_BODY    (SPEC_MAX_FRAME - SPEC_BODY_AT)

/* The header fields, by their offset in the frame. contract: docs/protocol.md:37-43 */
#define SPEC_AT_NUMBYTES 14
#define SPEC_AT_SUM      16
#define SPEC_AT_SEND     18
#define SPEC_AT_ACK      22
#define SPEC_AT_RETRY    26
#define SPEC_AT_CMD      28
#define SPEC_AT_NCMDS    29

/* contract: protocol/diginet.ksy enum `command`; docs/protocol.md:42 */
#define SPEC_CMD_DATA    0x00
#define SPEC_CMD_ACK     0xa0
#define SPEC_CMD_E0      0xe0
#define SPEC_CMD_E1      0xe1
#define SPEC_CMD_E2      0xe2
#define SPEC_CMD_E3      0xe3

/* contract: protocol/diginet.ksy `announce`: `unknown` (size 15), `version` (strz, size 9),
 * `name` (strz, size 9); docs/protocol.md:47 */
#define SPEC_ANN_UNKNOWN 15
#define SPEC_ANN_FIELD   9
#define SPEC_ANN_VERSION SPEC_ANN_UNKNOWN
#define SPEC_ANN_NAME    (SPEC_ANN_VERSION + SPEC_ANN_FIELD)
#define SPEC_ANN_MIN     (SPEC_ANN_NAME + SPEC_ANN_FIELD)

/* contract: docs/protocol.md:27, the Digidesign OUI a desk sends from */
static const uint8_t SPEC_OUI[3] = { 0x00, 0xa0, 0x7e };
/* contract: docs/protocol.md:31, the announce goes to ff:ff:ff:ff:ff:ff */
static const uint8_t SPEC_BCAST[SPEC_MAC] = { 0xff, 0xff, 0xff, 0xff, 0xff, 0xff };

/* ---- the command stream ----------------------------------------------------------------- */

/* contract: protocol/diginet.ksy `sysex` (maker valid: 0x13) and enum `sysex_function` */
#define SPEC_MAKER       0x13
#define SPEC_FN_RING     0x00
#define SPEC_FN_METER    0x10
#define SPEC_FN_LEDS     0x20
#define SPEC_FN_COUNTER  0x30
#define SPEC_FN_SCRIBBLE 0x40
#define SPEC_FN_SYSTEM   0x70

/* contract: docs/protocol.md:79 and :99, the fader touch is strip button 09 */
#define SPEC_BTN_TOUCH   0x09
/* contract: docs/protocol.md:100, the section zones */
#define SPEC_ZONE_FIRST  0x18
#define SPEC_ZONE_LAST   0x1d
/* contract: docs/protocol.md:89, the jog wheel is B0 5C dd */
#define SPEC_JOG_CC      0x5c
/* contract: docs/protocol.md:85-87, 24 V-Pots, B0 (40|tt) dd */
#define SPEC_VPOTS       24
/* contract: docs/protocol.md:75, a 10-bit fader position */
#define SPEC_FADER_MAX   1023
/* contract: docs/protocol.md:92-94, 15 ring LEDs */
#define SPEC_RING_LEDS   15
/* contract: docs/protocol.md:130, a thermometer over 14 bits */
#define SPEC_METER_BITS  14
/* contract: docs/protocol.md:135, 8 seven-segment digits */
#define SPEC_DIGITS      8

/* The two desks. contract: docs/protocol.md:47 (the announce names), :146 (the device byte),
 * :73 (24 faders), :123 (the ProControl's displays 00..07, 8 characters each), :118 (the
 * Control|24's 4 characters), :135 and :138 (the counter at 0x19, at 0x09) */
struct spec_desk {
	const char *name;
	uint8_t device;
	uint8_t strips;
	uint8_t chars;
	uint8_t counter;
};
static const struct spec_desk SPEC_C24 = { "CNTRL|24", 0x01, 24, 4, 0x19 };
static const struct spec_desk SPEC_PC = { "MAINUNIT", 0x00, 8, 8, 0x09 };

/* ---- the library's API, as its header promises it ---------------------------------------- */

/* The return codes. contract: include/diginet/diginet.h:58-72 */
#define SPEC_OK           0
#define SPEC_E_ARG        (-1)
#define SPEC_E_SHORT      (-2)
#define SPEC_E_ETHERTYPE  (-3)
#define SPEC_E_LENGTH     (-4)
#define SPEC_E_SPACE      (-5)
#define SPEC_E_TRUNCATED  (-6)
#define SPEC_E_NO_STATUS  (-7)
#define SPEC_E_STATUS     (-8)
#define SPEC_E_NOT_ANNOUNCE (-9)
#define SPEC_E_REFUSED    (-10)
#define SPEC_E_RANGE      (-11)

/* The event kinds. contract: include/diginet/diginet_codec.h:177-191 */
enum {
	SPEC_EV_FADER = 1, SPEC_EV_TOUCH, SPEC_EV_STRIP_BUTTON, SPEC_EV_SECTION_BUTTON,
	SPEC_EV_VPOT, SPEC_EV_JOG, SPEC_EV_RING, SPEC_EV_METER, SPEC_EV_STRIP_LEDS,
	SPEC_EV_SCRIBBLE, SPEC_EV_COUNTER, SPEC_EV_SYSTEM, SPEC_EV_OTHER,
};

/* The key of a command, kind << 16 | address. contract: include/diginet/diginet_codec.h:48-62 */
enum {
	SPEC_KEY_FADER = 1, SPEC_KEY_LED, SPEC_KEY_RING, SPEC_KEY_METER, SPEC_KEY_LEDS,
	SPEC_KEY_COUNTER, SPEC_KEY_SCRIBBLE, SPEC_KEY_INPUT, SPEC_KEY_KEEPALIVE,
};
#define SPEC_KEY(kind, addr) ((uint32_t)(kind) << 16 | ((uint32_t)(addr) & 0xffff))

/* The longest command an encoder makes. contract: include/diginet/diginet_codec.h:46 */
#define SPEC_CMD_MAX     24

/* ---- reading bytes ------------------------------------------------------------------------- */

static inline uint16_t spec_be16(const uint8_t *p)
{
	return (uint16_t)(p[0] << 8 | p[1]);
}

static inline uint32_t spec_be32(const uint8_t *p)
{
	return (uint32_t)p[0] << 24 | (uint32_t)p[1] << 16 | (uint32_t)p[2] << 8 | p[3];
}

static inline void spec_put16(uint8_t *p, unsigned v)
{
	p[0] = (uint8_t)(v >> 8);
	p[1] = (uint8_t)v;
}

static inline void spec_put32(uint8_t *p, uint32_t v)
{
	p[0] = (uint8_t)(v >> 24);
	p[1] = (uint8_t)(v >> 16);
	p[2] = (uint8_t)(v >> 8);
	p[3] = (uint8_t)v;
}

/* The header sum: the 16-bit additive sum of the body bytes, padding excluded.
 * contract: docs/protocol.md:38; protocol/diginet.ksy header `sum` */
static inline uint16_t spec_sum(const uint8_t *p, size_t n)
{
	unsigned s = 0;
	for (size_t i = 0; i < n; i++)
		s = (s + p[i]) & 0xffff;
	return (uint16_t)s;
}

/* ---- a frame ------------------------------------------------------------------------------- */

/* A frame as diginet.ksy reads it. `code` is what diginet.h:107-109 says the parser answers:
 * SPEC_E_SHORT for fewer bytes than the two headers, SPEC_E_ETHERTYPE for another EtherType,
 * SPEC_E_LENGTH for a numbytes under 16 (diginet.ksy header `numbytes` valid min: 16) or past
 * the end of the buffer, else SPEC_OK with the fields below. */
struct spec_frame {
	int code;
	const uint8_t *dst, *src;
	uint16_t ethertype, numbytes, sum, retry;
	uint32_t send, ack;
	uint8_t cmd, ncmds;
	const uint8_t *body;
	size_t body_len, pad_len;
	uint16_t body_sum;
};

static inline int spec_read_frame(const uint8_t *b, size_t len, struct spec_frame *f)
{
	memset(f, 0, sizeof *f);
	if (len < SPEC_BODY_AT)
		return f->code = SPEC_E_SHORT;
	f->ethertype = spec_be16(b + 12);
	if (f->ethertype != SPEC_ETHERTYPE)
		return f->code = SPEC_E_ETHERTYPE;
	f->numbytes = spec_be16(b + SPEC_AT_NUMBYTES);
	if (f->numbytes < SPEC_HDR || f->numbytes > len - SPEC_ETH_HDR)
		return f->code = SPEC_E_LENGTH;
	f->dst = b;
	f->src = b + SPEC_MAC;
	f->sum = spec_be16(b + SPEC_AT_SUM);
	f->send = spec_be32(b + SPEC_AT_SEND);
	f->ack = spec_be32(b + SPEC_AT_ACK);
	f->retry = spec_be16(b + SPEC_AT_RETRY);
	f->cmd = b[SPEC_AT_CMD];
	f->ncmds = b[SPEC_AT_NCMDS];
	f->body = b + SPEC_BODY_AT;
	f->body_len = f->numbytes - SPEC_HDR;
	f->pad_len = len - SPEC_BODY_AT - f->body_len;
	f->body_sum = spec_sum(f->body, f->body_len);
	return f->code = SPEC_OK;
}

/* The frame diginet_frame_build() owes for these fields (diginet.h:111-114): the two MACs,
 * 0x885F, numbytes 16 + body length, the body's sum or zero, the counters, retry, command
 * and count, the body, then zeros up to the 60-byte minimum. Returns its length. */
static inline size_t spec_build_frame(uint8_t *out, const uint8_t *dst, const uint8_t *src,
				      uint32_t send, uint32_t ack, uint16_t retry, uint8_t cmd,
				      uint8_t ncmds, const uint8_t *body, size_t len, int zero_sum)
{
	size_t n = SPEC_BODY_AT + len < SPEC_MIN_FRAME ? SPEC_MIN_FRAME : SPEC_BODY_AT + len;
	memset(out, 0, n);
	memcpy(out, dst, SPEC_MAC);
	memcpy(out + SPEC_MAC, src, SPEC_MAC);
	spec_put16(out + 12, SPEC_ETHERTYPE);
	spec_put16(out + SPEC_AT_NUMBYTES, (unsigned)(SPEC_HDR + len));
	spec_put16(out + SPEC_AT_SUM, zero_sum ? 0 : spec_sum(body, len));
	spec_put32(out + SPEC_AT_SEND, send);
	spec_put32(out + SPEC_AT_ACK, ack);
	spec_put16(out + SPEC_AT_RETRY, retry);
	out[SPEC_AT_CMD] = cmd;
	out[SPEC_AT_NCMDS] = ncmds;
	if (len)
		memcpy(out + SPEC_BODY_AT, body, len);
	return n;
}

/* A fixed string field of the announce: up to its first NUL, at most 9 bytes.
 * contract: protocol/diginet.ksy `announce` `version` and `name` (type: strz, size: 9) */
static inline size_t spec_strz_len(const uint8_t *p)
{
	size_t n = 0;
	while (n < SPEC_ANN_FIELD && p[n])
		n++;
	return n;
}

/* ---- the system family ---------------------------------------------------------------------- */

/* Where F0 13 xx 70 starts in a body, whole or cut short, or -1. A host never sends this
 * family: it writes the desk's memory (docs/protocol.md:140-144), and diginet.h:113-114 and
 * diginet_codec.h:172-173 say a body holding it is refused. contract: docs/protocol.md:140 */
static inline long spec_system_at(const uint8_t *b, size_t len)
{
	for (size_t i = 0; i + 3 < len; i++)
		if (b[i] == 0xf0 && b[i + 1] == SPEC_MAKER && b[i + 3] == SPEC_FN_SYSTEM)
			return (long)i;
	return -1;
}

/* ---- the command stream --------------------------------------------------------------------- */

/* One step of the command stream, as diginet.ksy `message` reads it, with running status
 * expanded (docs/protocol.md:71):
 *   - F0 runs to its first F7 and cancels running status (diginet.ksy `running_status_out`);
 *     with no F7 the message is cut short at the end of the body;
 *   - a status byte 80..EF, or a data byte under the running status in force, then one data
 *     byte for C0 and D0 and two for every other status (diginet.ksy `data2`), each under
 *     0x80;
 *   - a data byte with no running status is refused and stepped over, and so is a status
 *     byte F1..FF, which no message of the grammar carries and which clears running status
 *     (diginet.h:158-160);
 *   - a message whose data bytes run past the body is cut short at its end (diginet.h:158-160),
 *     whatever the bytes left are: one byte, too few for any message;
 *   - else a status byte where a data byte is due starts the next message (MIDI), so the
 *     message before it is cut short there and running status is cleared
 *     (src/diginet_msg.c:90).
 * `code` is 1 for a message, 0 at the end, or the refusal; `next` is where the following step
 * starts, and `status_out` the running status after this step. */
struct spec_msg {
	int code;
	size_t at, len, next;
	uint8_t status, running, d1, d2, status_out;
	size_t sysex_at, sysex_len;
};

static inline void spec_msg_step(const uint8_t *b, size_t len, size_t at, uint8_t status_in,
				 struct spec_msg *m)
{
	memset(m, 0, sizeof *m);
	m->at = at;
	m->status_out = status_in;
	if (at >= len) {
		m->code = 0;
		m->next = at;
		return;
	}
	uint8_t lead = b[at];
	if (lead == 0xf0) {
		size_t i = at + 1;
		while (i < len && b[i] != 0xf7)
			i++;
		m->status_out = 0;
		if (i == len) {
			m->code = SPEC_E_TRUNCATED;
			m->next = len;
			return;
		}
		m->code = 1;
		m->status = 0xf0;
		m->sysex_at = at + 1;
		m->sysex_len = i - at - 1;
		m->len = i + 1 - at;
		m->next = i + 1;
		return;
	}
	if (lead > 0xf0) {
		m->code = SPEC_E_STATUS;
		m->next = at + 1;
		m->status_out = 0;
		return;
	}
	if (lead < 0x80 && !status_in) {
		m->code = SPEC_E_NO_STATUS;
		m->next = at + 1;
		return;
	}
	uint8_t status = lead >= 0x80 ? lead : status_in;
	size_t data = lead >= 0x80 ? at + 1 : at;
	size_t n = (status & 0xf0) == 0xc0 || (status & 0xf0) == 0xd0 ? 1 : 2;
	if (data + n > len) {
		m->code = SPEC_E_TRUNCATED;
		m->next = len;
		return;
	}
	for (size_t k = 0; k < n; k++) {
		if (b[data + k] >= 0x80) {
			m->code = SPEC_E_TRUNCATED;
			m->next = data + k;
			m->status_out = 0;
			return;
		}
	}
	m->code = 1;
	m->status = status;
	m->running = lead < 0x80;
	m->d1 = b[data];
	m->d2 = n == 2 ? b[data + 1] : 0;
	m->len = data + n - at;
	m->next = data + n;
	m->status_out = status;
}

/* ---- the controls ---------------------------------------------------------------------------- */

/* The most characters a scribble write carries: the ProControl's 8. contract: docs/protocol.md:123 */
#define SPEC_CHARS_MAX   8

/* The segments a meter mask lights: n when the mask is the n lowest bits, n at most 14, else
 * -1, a mask that is no thermometer. contract: docs/protocol.md:130 */
static inline int spec_segments(unsigned mask)
{
	for (int n = 0; n <= SPEC_METER_BITS; n++)
		if (mask == (1u << n) - 1)
			return n;
	return -1;
}

/* The control a message is, as docs/protocol.md "The command set" gives each one. A fader
 * position here is the MSB's alone; its LSB is the next message's (spec_fader_lsb). */
struct spec_event {
	int kind;
	uint8_t strip, button, zone, on, right, addr, device, len, dots;
	uint16_t value, mask;
	int16_t delta;
	int8_t segments;
	uint8_t text[SPEC_CHARS_MAX];
	uint8_t seg[SPEC_DIGITS];
};

static inline void spec_event_of(const uint8_t *b, const struct spec_msg *m, struct spec_event *e)
{
	memset(e, 0, sizeof *e);
	e->kind = SPEC_EV_OTHER;
	uint8_t family = m->status & 0xf0;
	if (family == 0x90) {
		/* 90 bb (40 if on | id): docs/protocol.md:99-100, a zone 18..1D is a section
		 * button, else id is a strip, and button 09 on a strip is the fader touch (:79) */
		uint8_t id = m->d2 & 0x3f;
		e->button = m->d1;
		e->on = m->d2 >> 6 & 1;
		if (id >= SPEC_ZONE_FIRST && id <= SPEC_ZONE_LAST) {
			e->kind = SPEC_EV_SECTION_BUTTON;
			e->zone = id;
		} else {
			e->kind = m->d1 == SPEC_BTN_TOUCH ? SPEC_EV_TOUCH : SPEC_EV_STRIP_BUTTON;
			e->strip = id;
		}
		return;
	}
	if (family == 0xb0) {
		if (m->d1 < 0x20) {
			/* B0 tt MSB: docs/protocol.md:75, the position's top 7 bits */
			e->kind = SPEC_EV_FADER;
			e->strip = m->d1;
			e->value = (uint16_t)(m->d2 << 3);
		} else if (m->d1 == SPEC_JOG_CC) {
			e->kind = SPEC_EV_JOG;
			e->delta = (int16_t)(m->d2 - 64);
		} else if (m->d1 >= 0x40 && m->d1 < 0x40 + SPEC_VPOTS) {
			e->kind = SPEC_EV_VPOT;
			e->strip = (uint8_t)(m->d1 - 0x40);
			e->delta = (int16_t)(m->d2 - 64);
		}
		return;
	}
	if (m->status != 0xf0)
		return;
	const uint8_t *s = b + m->sysex_at;
	size_t n = m->sysex_len;
	if (n < 3 || s[0] != SPEC_MAKER)
		return;
	e->device = s[1];
	const uint8_t *pl = s + 3;
	size_t pn = n - 3;
	switch (s[2]) {
	case SPEC_FN_RING:
		/* (tt | 40 if LED 1) b1 b2: docs/protocol.md:94, b1 bits 6..0 LEDs 2..8, b2 bits
		 * 6..0 LEDs 9..15; LED L is bit L - 1 of the mask (diginet_codec.h:103) */
		if (pn != 3)
			return;
		e->kind = SPEC_EV_RING;
		e->strip = pl[0] & 0x3f;
		e->mask = pl[0] >> 6 & 1;
		for (unsigned led = 2; led <= SPEC_RING_LEDS; led++) {
			uint8_t byte = led <= 8 ? pl[1] : pl[2];
			unsigned bit = led <= 8 ? 8 - led : 15 - led;
			if (byte >> bit & 1)
				e->mask |= (uint16_t)(1u << (led - 1));
		}
		return;
	case SPEC_FN_METER:
		/* ch hi lo: docs/protocol.md:129-130, ch | 20 for the right side, hi the mask's
		 * top 7 bits and lo its low 7 */
		if (pn != 3)
			return;
		e->kind = SPEC_EV_METER;
		e->addr = pl[0];
		e->strip = pl[0] & 0x1f;
		e->right = pl[0] >> 5 & 1;
		e->mask = (uint16_t)((pl[1] & 0x7f) << 7 | (pl[2] & 0x7f));
		e->segments = (int8_t)spec_segments(e->mask);
		return;
	case SPEC_FN_LEDS:
		/* tt bits: docs/protocol.md:112-113 */
		if (pn != 2)
			return;
		e->kind = SPEC_EV_STRIP_LEDS;
		e->addr = pl[0];
		e->strip = pl[0];
		e->mask = pl[1];
		return;
	case SPEC_FN_SCRIBBLE:
		/* aa 00 c1..cN: docs/protocol.md:118, at most 8 characters (:123) */
		if (pn < 3 || pn - 2 > SPEC_CHARS_MAX)
			return;
		e->kind = SPEC_EV_SCRIBBLE;
		e->addr = pl[0];
		e->len = (uint8_t)(pn - 2);
		memcpy(e->text, pl + 2, e->len);
		return;
	case SPEC_FN_COUNTER:
		/* aa dots d8..d1: docs/protocol.md:135, the rightmost digit first */
		if (pn != 2 + SPEC_DIGITS)
			return;
		e->kind = SPEC_EV_COUNTER;
		e->addr = pl[0];
		e->dots = pl[1];
		for (unsigned k = 0; k < SPEC_DIGITS; k++)
			e->seg[k] = pl[2 + SPEC_DIGITS - 1 - k];
		return;
	case SPEC_FN_SYSTEM:
		e->kind = SPEC_EV_SYSTEM;
		return;
	default:
		return;
	}
}

#endif /* DIGINET_FUZZ_SPEC_H */
