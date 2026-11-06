// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>

/* libFuzzer harness: THE COMMAND GRAMMAR (src/diginet_msg.c, src/diginet_decode.c and the
 * refusal of src/diginet_codec.c), the reading of protocol/diginet.ksy's `commands`,
 * `message` and `sysex` over the body of a data frame, and the controls made of it.
 *
 * Input: [sel] then the rest.
 *   sel % 3 picks the personality the decoder is given: none (the decoder's default),
 *   Control|24, ProControl.
 *   sel & 0x80: the rest is one whole Ethernet frame, and the body the grammar reads in it
 *   (fuzz/spec.h, spec_read_frame) is decoded; a frame the grammar refuses decodes as an
 *   empty body. Otherwise the rest is the body itself.
 * The rest is copied into an allocation of exactly its length.
 *
 * The harness reads the body itself, step by step, from the grammar (spec_msg_step) and the
 * controls from docs/protocol.md (spec_event_of), and holds the library's cursor, its decoder
 * and its refusal to that reading. No expected value comes from the library.
 *
 * Properties, each an abort() in a check_ function:
 *   - cursor: diginet_msg_next() gives each step of the grammar in turn: the end only at
 *     the end; a message where the grammar has one, with its place, length, status, running
 *     flag and data bytes, or its sysex payload between F0 and the first F7; a refusal where
 *     the grammar refuses (a data byte with no running status, a status byte F1..FF, a
 *     message cut short), with the cursor where the next step starts and the running status
 *     the grammar leaves in force.
 *   - events: diginet_decoder_next() gives the same steps as controls: a refusal as the
 *     cursor's code, and a message as the event docs/protocol.md makes of it, carrying that
 *     message: a key, a touch or a zone key with its button, strip or zone and state; a fader
 *     whose LSB is the next message exactly when that is B0 (20+tt); a jog or a V-Pot with its
 *     delta; a ring, a meter, LEDs, a scribble write or the counter with every field; the
 *     system family as DIGINET_EV_SYSTEM; the device byte of each sysex; anything else OTHER.
 *   - refusal: diginet_body_check() refuses a body exactly when F0 13 xx 70 is in it, whole or
 *     cut short.
 */
#include <diginet/diginet.h>
#include <diginet/diginet_codec.h>

#include "fuzz.h"

FUZZ_CHECK check_cursor_step(const struct spec_msg *m, int r, const struct diginet_cursor *c)
{
	/* The cursor ends exactly where the body ends.
	 * contract: protocol/diginet.ksy `commands` (messages, repeat: eos); diginet.h:158
	 * mutant: src/diginet_msg.c:32 `return 0;` -> `return 2;`
	 * input: keepalive */
	if ((m->code == 0) != (r == 0))
		abort();
	/* A data byte with no running status in force is refused as such.
	 * contract: protocol/diginet.ksy `message` `status` (0 for none); diginet.h:66, :158-159
	 * mutant: src/diginet_msg.c:76 `DIGINET_E_NO_STATUS` -> `DIGINET_E_STATUS`
	 * input: no-status */
	if (m->code == SPEC_E_NO_STATUS && r != SPEC_E_NO_STATUS)
		abort();
	/* A status byte F1..FF, which no message carries, is refused as such.
	 * contract: protocol/diginet.ksy `message` (`lead`: F0 or a channel status); diginet.h:67
	 * mutant: src/diginet_msg.c:64 `lead >= 0xf0` -> `lead > 0xf1`
	 * input: status-f1 */
	if (m->code == SPEC_E_STATUS && r != SPEC_E_STATUS)
		abort();
	/* A message cut short, by the end of the body or by a status byte where a data byte is
	 * due, is refused as truncated.
	 * contract: protocol/diginet.ksy `sysex` `payload` (terminator: 0xf7) and `data2`;
	 * diginet.h:65
	 * mutant: src/diginet_msg.c:48 `i >= c->len` -> `i > c->len`
	 * input: sysex-no-f7 */
	if (m->code == SPEC_E_TRUNCATED && r != SPEC_E_TRUNCATED)
		abort();
	/* A message the grammar reads is given as a message.
	 * contract: protocol/diginet.ksy `message`
	 * mutant: src/diginet_msg.c:89 `b[data_at + i] & 0x80` -> `b[data_at + i] & 0x40`
	 * input: button_mute */
	if (m->code == 1 && r != 1)
		abort();
	/* The cursor stands where the grammar's next step starts: after the message, after the
	 * refused byte, at the end, or at the status byte that cut a message short.
	 * contract: diginet.h:158-160; src/diginet_msg.c:90
	 * mutant: src/diginet_msg.c:91 `c->pos = data_at + i;` -> `c->pos = data_at + i + 1;`
	 * input: status-for-data */
	if (c->pos != m->next)
		abort();
	/* The running status in force afterwards is the grammar's: the message's channel status,
	 * none after a system exclusive or a refused status byte, unchanged otherwise.
	 * contract: protocol/diginet.ksy `message` `running_status_out`; docs/protocol.md:71
	 * mutant: src/diginet_msg.c:101 `c->status = status;` -> `c->status = 0;`
	 * input: running_status
	 * mutant: src/diginet_msg.c:47 `c->status = 0;` -> `c->status = c->status;`
	 * input: status-cancelled */
	if (c->status != m->status_out)
		abort();
}

FUZZ_CHECK check_cursor_message(const uint8_t *b, const struct spec_msg *m, const struct diginet_msg *msg)
{
	/* The message starts at the cursor's place and takes the bytes the grammar gives it.
	 * contract: protocol/diginet.ksy `message`; diginet.h:138-147
	 * mutant: src/diginet_msg.c:99 `m->len = data_at + n - start;` -> `m->len = data_at + n - start + 1;`
	 * input: button_mute */
	if (msg->offset != m->at || msg->len != m->len)
		abort();
	/* Its status is the status byte or the running status in force, and its data bytes are
	 * the one (C0, D0) or two that follow.
	 * contract: protocol/diginet.ksy `message` `status`, `running`, `data1`, `data2`
	 * mutant: src/diginet_msg.c:98 `b[data_at + 1]` -> `b[data_at]`
	 * input: button_mute */
	if (msg->status != m->status || msg->running != m->running || msg->d1 != m->d1 ||
	    msg->d2 != m->d2)
		abort();
	/* A system exclusive's payload is the bytes between F0 and its first F7.
	 * contract: protocol/diginet.ksy `sysex` (terminator: 0xf7); diginet.h:143-144
	 * mutant: src/diginet_msg.c:55 `m->sysex_len = i - start - 1;` -> `m->sysex_len = i - start;`
	 * input: scribble_write */
	if (m->status == 0xf0 && (msg->sysex != b + m->sysex_at || msg->sysex_len != m->sysex_len))
		abort();
}

/* what the decoder owes for the step at `at`: the step, the control, and where the next step
 * starts (after the fader's LSB when it took one) */
struct owed {
	struct spec_msg m;
	struct spec_event e;
	int lsb_missing;
	size_t next;
	uint8_t status_out;
};

static void owed_at(const uint8_t *b, size_t len, size_t at, uint8_t status, struct owed *o)
{
	spec_msg_step(b, len, at, status, &o->m);
	o->next = o->m.next;
	o->status_out = o->m.status_out;
	o->lsb_missing = 0;
	memset(&o->e, 0, sizeof o->e);
	if (o->m.code != 1)
		return;
	spec_event_of(b, &o->m, &o->e);
	if (o->e.kind != SPEC_EV_FADER)
		return;
	/* B0 tt MSB (20+tt) LSB, the LSB's top three bits the position's low three
	 * (docs/protocol.md:75): the next message, when it is that control change */
	struct spec_msg lsb;
	spec_msg_step(b, len, o->m.next, o->m.status_out, &lsb);
	if (lsb.code == 1 && (lsb.status & 0xf0) == 0xb0 && lsb.d1 == 0x20 + o->m.d1) {
		o->e.value |= (uint16_t)(lsb.d2 >> 4 & 7);
		o->next = lsb.next;
		o->status_out = lsb.status_out;
	} else {
		o->lsb_missing = 1;
	}
}

FUZZ_CHECK check_events_step(const uint8_t *b, const struct owed *o, int rd, const struct diginet_event *ev)
{
	const struct spec_msg *m = &o->m;
	/* The decoder gives what the cursor gives: a message, a refusal with its code, or the end.
	 * contract: diginet_codec.h:216; diginet.h:158-160
	 * mutant: src/diginet_decode.c:114 `return r;` -> `return 0;`
	 * input: status-for-data
	 * mutant: src/diginet_decode.c:140 `d->c = peek;` -> `d->c = d->c;`
	 * input: fader_move */
	if (rd != m->code)
		abort();
	if (rd != 1)
		return;
	/* The event carries the message it came from.
	 * contract: diginet_codec.h:205
	 * mutant: src/diginet_decode.c:116 `ev->msg = m;` -> `ev->msg.offset = m.offset;`
	 * input: button_mute
	 * mutant: src/diginet_decode.c:116 `ev->msg = m;` -> `ev->msg = m, ev->msg.running = 0;`
	 * input: running_status */
	if (ev->msg.offset != m->at || ev->msg.len != m->len || ev->msg.status != m->status ||
	    ev->msg.running != m->running || ev->msg.d1 != m->d1 || ev->msg.d2 != m->d2 ||
	    (m->status == 0xf0 && (ev->msg.sysex != b + m->sysex_at || ev->msg.sysex_len != m->sysex_len)))
		abort();
	/* The event is the control docs/protocol.md makes of the message.
	 * contract: docs/protocol.md:75-146; fuzz/spec.h spec_event_of
	 * mutant: src/diginet_decode.c:28 `m->d1 == DIGINET_BTN_TOUCH` -> `m->d1 == 0x0a`
	 * input: touch
	 * mutant: src/diginet_decode.c:100 `DIGINET_EV_SYSTEM` -> `DIGINET_EV_OTHER`
	 * input: system-whole
	 * mutant: src/diginet_decode.c:51 `pn != 3` -> `pn > 3`
	 * input: sysex-wrong-sizes */
	if ((int)ev->kind != o->e.kind)
		abort();
}

FUZZ_CHECK check_events_fields(const uint8_t *b, const struct owed *o, const struct diginet_event *ev)
{
	const struct spec_event *e = &o->e;
	int maker = o->m.status == 0xf0 && o->m.sysex_len >= 3 && b[o->m.sysex_at] == SPEC_MAKER;
	int key = e->kind == SPEC_EV_TOUCH || e->kind == SPEC_EV_STRIP_BUTTON || e->kind == SPEC_EV_SECTION_BUTTON;
	/* A key, a touch or a zone key: its button, whether it is down, its strip or its zone.
	 * contract: docs/protocol.md:79, :99-100
	 * mutant: src/diginet_decode.c:23 `(m->d2 & 0x40) != 0` -> `(m->d2 & 0x20) != 0`
	 * input: button_mute */
	if (key && (ev->button != e->button || ev->on != e->on ||
		    (e->kind == SPEC_EV_SECTION_BUTTON ? ev->zone != e->zone : ev->strip != e->strip)))
		abort();
	/* A fader: its strip, the position MSB << 3 | LSB >> 4, and whether the LSB came.
	 * contract: docs/protocol.md:75-76; diginet_codec.h:178
	 * mutant: src/diginet_decode.c:139 `(lsb.d2 >> 4) & 7` -> `(lsb.d2 >> 3) & 7`
	 * input: running_status
	 * mutant: src/diginet_decode.c:134 `(uint16_t)(m.d2 << 3)` -> `(uint16_t)(m.d2 << 2)`
	 * input: fader_move
	 * mutant: src/diginet_decode.c:142 `ev->lsb_missing = 1;` -> `ev->lsb_missing = 0;`
	 * input: fader-msb-only */
	if (e->kind == SPEC_EV_FADER &&
	    (ev->strip != e->strip || ev->value != e->value || ev->lsb_missing != o->lsb_missing))
		abort();
	/* A jog or a V-Pot: its strip and the delta dd - 64.
	 * contract: docs/protocol.md:87, :89
	 * mutant: src/diginet_decode.c:154 `(int16_t)(m.d2 - 64)` -> `(int16_t)(m.d2 - 63)`
	 * input: jog-vpot */
	if ((e->kind == SPEC_EV_JOG || e->kind == SPEC_EV_VPOT) &&
	    (ev->delta != e->delta || (e->kind == SPEC_EV_VPOT && ev->strip != e->strip)))
		abort();
	/* A ring: its strip and the 15 LEDs it lights, LED 1 from the address byte.
	 * contract: docs/protocol.md:94
	 * mutant: src/diginet_decode.c:58 `(1u << (1 + k))` -> `(1u << (2 + k))`
	 * input: ring */
	if (e->kind == SPEC_EV_RING && (ev->strip != e->strip || ev->mask != e->mask))
		abort();
	/* A meter: its channel and side, its 14-bit mask and the segments that lights, or -1.
	 * contract: docs/protocol.md:129-130
	 * mutant: src/diginet_decode.c:69 `(pl[0] & 0x20) != 0` -> `(pl[0] & 0x10) != 0`
	 * input: meter-right
	 * mutant: src/diginet_codec.c:214 `(mask >> n) ? -1 : n` -> `n`
	 * input: meter-not-thermometer
	 * mutant: src/diginet_codec.c:212 `n < DIGINET_METER_SEGMENTS` -> `n < 13`
	 * input: meter-right */
	if (e->kind == SPEC_EV_METER &&
	    (ev->addr != e->addr || ev->strip != e->strip || ev->right != e->right ||
	     ev->mask != e->mask || ev->segments != e->segments))
		abort();
	/* LEDs: the address and the bits.
	 * contract: docs/protocol.md:112-113
	 * mutant: src/diginet_decode.c:79 `ev->mask = pl[1];` -> `ev->mask = pl[0];`
	 * input: strip-leds */
	if (e->kind == SPEC_EV_STRIP_LEDS &&
	    (ev->addr != e->addr || ev->strip != e->strip || ev->mask != e->mask))
		abort();
	/* A scribble write: the address and its characters, NUL-terminated.
	 * contract: docs/protocol.md:118, :123
	 * mutant: src/diginet_decode.c:87 `pl + 2` -> `pl + 1`
	 * input: scribble_write */
	if (e->kind == SPEC_EV_SCRIBBLE &&
	    (ev->addr != e->addr || ev->len != e->len || memcmp(ev->text, e->text, e->len) ||
	     ev->text[e->len] != '\0'))
		abort();
	/* The counter: the address, the dots, and the digits left to right as shown.
	 * contract: docs/protocol.md:135-137
	 * mutant: src/diginet_decode.c:97 `DIGINET_COUNTER_DIGITS - 1 - k` -> `k`
	 * input: counter_write */
	if (e->kind == SPEC_EV_COUNTER &&
	    (ev->addr != e->addr || ev->dots != e->dots || memcmp(ev->seg, e->seg, SPEC_DIGITS)))
		abort();
	/* Every sysex of the maker 13 carries its device byte, whatever its function.
	 * contract: docs/protocol.md:146; protocol/diginet.ksy `sysex` `device`
	 * mutant: src/diginet_decode.c:46 `ev->device = s[1];` -> `ev->device = s[2];`
	 * input: meter */
	if (maker && ev->device != e->device)
		abort();
}

FUZZ_CHECK check_refusal(const uint8_t *b, size_t len)
{
	int want = spec_system_at(b, len) >= 0 ? SPEC_E_REFUSED : SPEC_OK;
	/* A body is refused exactly when it holds F0 13 xx 70, whole or cut short.
	 * contract: docs/protocol.md:140-144; diginet_codec.h:172-173
	 * mutant: src/diginet_codec.c:59 `i + 3 < len` -> `i + 4 < len`
	 * input: system-cut-short
	 * mutant: src/diginet_codec.c:55 `m.sysex[0] == DIGINET_SYSEX_MAKER &&` -> ``
	 * input: system-other-maker */
	if (diginet_body_check(b, len) != want)
		abort();
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	static const enum diginet_desk DESK[3] = {
		DIGINET_DESK_UNKNOWN, DIGINET_DESK_CONTROL24, DIGINET_DESK_PROCONTROL,
	};
	struct spec_frame w;
	struct diginet_cursor c;
	struct diginet_decoder d;
	struct diginet_msg msg;
	struct diginet_event ev;

	if (size >= FUZZ_INPUT_MAX || size == 0)
		return 0;
	uint8_t sel = data[0];
	uint8_t *buf = fuzz_dup(data + 1, size - 1);
	const uint8_t *body = buf;
	size_t len = size - 1;
	if (sel & 0x80) {
		if (spec_read_frame(buf, len, &w) == SPEC_OK) {
			body = w.body;
			len = w.body_len;
		} else {
			len = 0;
		}
	}

	/* the cursor, a step of the grammar at a time; each step moves forward, so this ends
	 * within len + 1 steps */
	diginet_cursor_init(&c, body, len);
	size_t at = 0;
	uint8_t status = 0;
	for (size_t steps = 0; steps <= len; steps++) {
		struct spec_msg m;
		spec_msg_step(body, len, at, status, &m);
		memset(&msg, 0, sizeof msg);
		int r = diginet_msg_next(&c, &msg);
		check_cursor_step(&m, r, &c);
		if (m.code == 1)
			check_cursor_message(body, &m, &msg);
		if (m.code == 0)
			break;
		at = m.next;
		status = m.status_out;
	}

	/* the decoder, the same way */
	diginet_decoder_init(&d, diginet_personality_of(DESK[sel % 3]), body, len);
	at = 0;
	status = 0;
	for (size_t steps = 0; steps <= len; steps++) {
		struct owed o;
		owed_at(body, len, at, status, &o);
		memset(&ev, 0, sizeof ev);
		int rd = diginet_decoder_next(&d, &ev);
		check_events_step(body, &o, rd, &ev);
		if (o.m.code == 1)
			check_events_fields(body, &o, &ev);
		if (o.m.code == 0)
			break;
		at = o.next;
		status = o.status_out;
	}

	check_refusal(body, len);
	free(buf);
	return 0;
}
