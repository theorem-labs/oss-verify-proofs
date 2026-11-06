// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>
// Modified by Theorem Labs, 2026-10-25: a modified copy of fuzz/fuzz_ctrl.c at libreac 9ed322ef.

/* libFuzzer harness: the CONTROL PLANE parsers (src/reac_ctrlblk.c, src/reac_ctrl.c,
 * src/reac_ports.c) — what a frame is, which box sent it, and what it declared.
 *
 * Input:  [0..5]  our MAC, the address a frame must be unicast to to reach us
 *         [6]     bit 0 set: run the builder round trip below, with the catalogue
 *                 row (byte >> 1) modulo the catalogue size
 *         [7..]   frames, each a u16 LE length then its bytes, at most 256 of them
 *
 * Every frame goes through reac_ctrl_parse, the single-record identity reply, the
 * two-fragment identity reassembly (stateful across frames, as on the wire), the
 * head-amp record check, the port-table decode, the master-side box classifier
 * and the catalogue match. Each frame is its own allocation of exactly its length.
 *
 * The harness computes each checksum itself (the block sum and the 7-bit DT1
 * record sum). It does not use the library's own checksum functions as the
 * expected value.
 *
 * Properties, each an abort():
 *   - reac_ctrl_parse is NONE exactly for a frame shorter than 50 B or not 0x8819,
 *     it reads the addresses and counter where the frame carries them, and it is
 *     FILLER exactly for type 00 00;
 *   - the block checksum and the head-amp record checksum agree with the sums;
 *   - the box classifier only answers for a Roland-OUI source that is not us and,
 *     FILLER (type 00 00) aside, only for a frame whose block checksum closes;
 *   - an identity payload is where the record puts it, inside the frame (or the
 *     reassembly buffer), and only ever comes out of a record whose block and
 *     record checksums close, under the address that the record (or the FIRST
 *     and LAST fragments, joined) carries; a frame whose block checksum does
 *     not close does not change the reassembly state;
 *   - a decoded port table counts each slot code as its own kind, in whole
 *     4-channel slots, and names the first unknown code;
 *   - a catalogue row comes only from a config-announce, and it is the first row
 *     whose declaration is the frame's block;
 *   - THE BUILDERS AND THE PARSERS AGREE: what reac_ctrl_build_as emits for a
 *     catalogue row parses back as the kind it is, matches that row, declares the
 *     row's widths, and its identity records reassemble to the row's own facts.
 *
 * Each property has, in its comment, one or more pairs of lines "mutant:" and
 * "input:". A mutant is a one-line change to libreac that makes the property
 * fail. The input is the seed in fuzz_ctrl_seed_corpus.zip that shows it.
 */
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include <reac/reac.h>
#include <reac/reac_ctrl.h>
#include <reac/reac_ctrlblk.h>
#include <reac/reac_identity.h>
#include <reac/reac_master.h>
#include <reac/reac_ports.h>

#include "fuzz.h"

#define MAX_FRAMES 256

static int inside(const uint8_t *p, size_t n, const uint8_t *base, size_t len)
{
	return p >= base && (size_t)(p - base) <= len && n <= len - (size_t)(p - base);
}

/* 1 when the 32-byte control block frame[18..50) sums to 0 mod 256. The caller
 * makes sure that the frame has 50 bytes. */
static int block_sum_closes(const uint8_t *frame)
{
	unsigned s = 0;
	for (int i = REAC_CTRL_BLOCK_OFF; i < REAC_CTRL_BLOCK_END; i++)
		s += frame[i];
	return (s & 0xff) == 0;
}

/* 1 when the n bytes of a Roland DT1 record (TAG to CKSUM) sum to 0 mod 128. */
static int record_sum_closes(const uint8_t *rec, size_t n)
{
	unsigned s = 0;
	for (size_t i = 0; i < n; i++)
		s += rec[i];
	return (s & 0x7f) == 0;
}

static int known_slot(uint8_t code)
{
	return code == REAC_PORT_SLOT_IN || code == REAC_PORT_SLOT_IN_SPLIT ||
	       code == REAC_PORT_SLOT_OUT || code == REAC_PORT_SLOT_EMPTY;
}

static void check_ports(const uint8_t *block)
{
	struct reac_box_ports ports = { -7, -7, -7 };
	int r = reac_ports_parse(block, &ports);
	uint8_t first = 0xee;
	int unk = reac_ports_unknown(block, &first);
	/* A NULL first_code gives the same count.
	 * mutant: src/reac_ports.c:53 `!block` -> `!block || !first_code`
	 * input: fixture-l1-decl-82 */
	if (reac_ports_unknown(block, NULL) != unk)
		abort();
	/* Both doors refuse the same blocks: a complete link-1 declaration or nothing.
	 * mutant: src/reac_ports.c:17 `REAC_SEG_SINGLE` -> `REAC_SEG_FIRST`
	 * input: fixture-l1-decl-82
	 * mutant: src/reac_ports.c:55 `REAC_SEG_SINGLE` -> `REAC_SEG_FIRST`
	 * input: fixture-l1-decl-82 */
	if ((r == 0) != (unk >= 0))
		abort();
	if (r != 0) {
		/* A refused parse leaves out untouched.
		 * mutant: src/reac_ports.c:18 `return -1;` -> `return out->in_ch = 0, -1;`
		 * input: fixture-filler
		 * mutant: src/reac_ports.c:18 `return -1;` -> `return out->out_ch = 0, -1;`
		 * input: fixture-filler
		 * mutant: src/reac_ports.c:18 `return -1;` -> `return out->headamp_base = 0, -1;`
		 * input: fixture-filler */
		if (ports.in_ch != -7 || ports.out_ch != -7 || ports.headamp_base != -7)
			abort();
		return;
	}
	int n_in = 0, n_out = 0, empty = 0;
	uint8_t want_first = 0;
	for (int i = 0; i < REAC_PORTS_TABLE_SLOTS; i++) {
		uint8_t code = block[REAC_PORTS_TABLE_OFF + i];
		n_in += code == REAC_PORT_SLOT_IN || code == REAC_PORT_SLOT_IN_SPLIT;
		n_out += code == REAC_PORT_SLOT_OUT;
		empty += code == REAC_PORT_SLOT_EMPTY;
		/* No unknown code is 0 (0 is the split input), so 0 means "none yet". */
		if (!known_slot(code) && want_first == 0)
			want_first = code;
	}
	/* The widths are whole 4-channel slots.
	 * mutant: src/reac_ports.c:40 `* REAC_PORTS_CH_PER_SLOT;` -> `* REAC_PORTS_CH_PER_SLOT + 1;`
	 * input: fixture-l1-decl-82
	 * mutant: src/reac_ports.c:41 `* REAC_PORTS_CH_PER_SLOT;` -> `* REAC_PORTS_CH_PER_SLOT + 1;`
	 * input: fixture-l1-decl-82
	 * mutant: src/reac_ports.c:70 `* REAC_PORTS_CH_PER_SLOT;` -> `* REAC_PORTS_CH_PER_SLOT + 1;`
	 * input: fixture-l1-decl-82 */
	if (ports.in_ch % REAC_PORTS_CH_PER_SLOT || ports.out_ch % REAC_PORTS_CH_PER_SLOT ||
	    unk % REAC_PORTS_CH_PER_SLOT)
		abort();
	/* first_code names the FIRST slot nobody has captured, and is 0 when there is
	 * none. The harness finds that slot itself.
	 * mutant: src/reac_ports.c:66 `unknown == 0 && first_code` -> `first_code`
	 * input: decl-two-unknown-slots
	 * mutant: src/reac_ports.c:67 `*first_code = code;` -> `*first_code = code + 1;`
	 * input: breakages
	 * mutant: src/reac_ports.c:65 `continue;` -> `{ if (first_code) *first_code = code; continue; }`
	 * input: fixture-l1-decl-82 */
	if (first != want_first)
		abort();
	/* Every one of the twelve slots is an input, an output, empty or unknown.
	 * mutant: src/reac_ports.c:70 `unknown * REAC_PORTS_CH_PER_SLOT` -> `(unknown + 1) * REAC_PORTS_CH_PER_SLOT`
	 * input: fixture-l1-decl-82 */
	if (ports.in_ch + ports.out_ch + unk + empty * REAC_PORTS_CH_PER_SLOT !=
	    REAC_PORTS_TABLE_SLOTS * REAC_PORTS_CH_PER_SLOT)
		abort();
	/* An input slot (02, or 00 split) counts as input, and an 01 slot as output.
	 * mutant: src/reac_ports.c:30 `out_slots++;` -> `in_slots++;`
	 * input: fixture-l1-decl-82
	 * mutant: src/reac_ports.c:29 `in_slots++;` -> `out_slots++;`
	 * input: fixture-l1-decl-82 */
	if (ports.in_ch != n_in * REAC_PORTS_CH_PER_SLOT ||
	    ports.out_ch != n_out * REAC_PORTS_CH_PER_SLOT)
		abort();
	/* The head-amp base is the chassis strap at block[7] times 0x10.
	 * mutant: src/reac_ports.c:45 `REAC_HEADAMP_BASE_MULTIPLIER` -> `8`
	 * input: fixture-l1-decl-82 */
	if (ports.headamp_base != block[REAC_HEADAMP_BASE_OFF] * REAC_HEADAMP_BASE_MULTIPLIER)
		abort();
}

/* The declaration a row sends, built here and not by libreac's synthesiser. A
 * captured row's declaration is its captured config_block. Any other row's is the
 * grammar: 01 03 00 10, the selector, 00 00, the head-amp strap, the twelve slot
 * codes in the row's declared order (inputs first as 02, or outputs first and the
 * inputs as 00), 03 for each slot left, the 11-byte tail, and the check byte that
 * makes the 32 bytes sum to 0 mod 256. 0 when the twelve slots cannot hold the
 * row's widths, so the row has no declaration.
 * contract: include/reac/reac_ctrlblk.h:432-434 (the grammar), :440-443 (the check
 * byte), :448-454 (a CAPTURED row carries its bytes), :456-472 (port_layout);
 * include/reac/reac_ports.h:89-96 (the table offset, twelve slots of 4 channels,
 * the slot codes) */
static int declaration_of(const struct reac_box_model *m, uint8_t out[REAC_CTRL_BLOCK_LEN])
{
	if (m->origin == REAC_BOX_CAPTURED) {
		memcpy(out, m->config_block, REAC_CTRL_BLOCK_LEN);
		return 1;
	}
	if (m->in_ch < 0 || m->out_ch < 0 || m->in_ch % REAC_PORTS_CH_PER_SLOT ||
	    m->out_ch % REAC_PORTS_CH_PER_SLOT)
		return 0;
	int in_slots = m->in_ch / REAC_PORTS_CH_PER_SLOT;
	int out_slots = m->out_ch / REAC_PORTS_CH_PER_SLOT;
	if (in_slots + out_slots > REAC_PORTS_TABLE_SLOTS)
		return 0;
	static const uint8_t head[4] = { 0x01, 0x03, 0x00, 0x10 };
	memcpy(out, head, sizeof head);
	out[4] = m->selector;
	out[5] = 0x00;
	out[6] = 0x00;
	out[7] = m->headamp_strap;
	uint8_t *slot = out + REAC_PORTS_TABLE_OFF;
	int k = 0;
	if (m->port_layout == REAC_BOX_PORTS_SPLIT_OUT_FIRST) {
		for (int i = 0; i < out_slots; i++)
			slot[k++] = REAC_PORT_SLOT_OUT;
		for (int i = 0; i < in_slots; i++)
			slot[k++] = REAC_PORT_SLOT_IN_SPLIT;
	} else {
		for (int i = 0; i < in_slots; i++)
			slot[k++] = REAC_PORT_SLOT_IN;
		for (int i = 0; i < out_slots; i++)
			slot[k++] = REAC_PORT_SLOT_OUT;
	}
	while (k < REAC_PORTS_TABLE_SLOTS)
		slot[k++] = REAC_PORT_SLOT_EMPTY;
	memcpy(slot + REAC_PORTS_TABLE_SLOTS, m->tail, sizeof m->tail);
	unsigned s = 0;
	for (int i = 0; i < REAC_CTRL_BLOCK_LEN - 1; i++)
		s += out[i];
	out[REAC_CTRL_BLOCK_LEN - 1] = (uint8_t)(0x100u - (s & 0xffu));
	return 1;
}

/* The first catalogue row whose declaration (declaration_of) is this block, or
 * NULL. */
static const struct reac_box_model *row_of_block(const uint8_t *block)
{
	size_t count = 0;
	const struct reac_box_model *cat = reac_box_catalogue(&count);
	for (size_t i = 0; cat && i < count; i++) {
		uint8_t blk[REAC_CTRL_BLOCK_LEN];
		if (declaration_of(&cat[i], blk) && memcmp(block, blk, sizeof blk) == 0)
			return &cat[i];
	}
	return NULL;
}

/* The body of the last FIRST fragment, read by the harness from the frame:
 * block[8] bytes from block[9]. */
struct first_frag {
	int have;
	uint8_t n;
	uint8_t body[REAC_CTRL_BLOCK_LEN];
};

/* Byte i of the record that the FIRST fragment and a LAST fragment (its block)
 * join: the FIRST body, then the LAST body from last[9]. */
static uint8_t joined_byte(const struct first_frag *first, const uint8_t *last, unsigned i)
{
	return i < first->n ? first->body[i] : last[9 + i - first->n];
}

/* 1 when the frame opens an identity record: a cd ea link-4 FIRST fragment with
 * the wrapper 00 02 00 fe, a body of 1 to 22 bytes (it ends before the check
 * byte), and a block that sums to 0 mod 256. A newer FIRST replaces an older one.
 * contract: reac.ksy:1897-1908 (link 4, segment FIRST, the wrapper at block[4:8],
 * the length echo at block[8], that many bytes after it);
 * include/reac/reac_ctrlblk.h:88, :91 (REAC_LINK_RECORD, REAC_SEG_FIRST), :620-628
 * (a FIRST is kept; both block checksums close) */
static int opens_record(const uint8_t *frame, size_t len, int sum_ok)
{
	if (len < REAC_CTRL_BLOCK_END || !sum_ok)
		return 0;
	const uint8_t *b = frame + REAC_CTRL_BLOCK_OFF;
	return frame[16] == 0xcd && frame[17] == 0xea && b[0] == REAC_LINK_RECORD &&
	       b[1] == REAC_SEG_FIRST && b[4] == 0x00 && b[5] == 0x02 && b[6] == 0x00 &&
	       b[7] == 0xfe && b[8] >= 1 && 9 + b[8] <= REAC_CTRL_BLOCK_LEN - 1;
}

static void fuzz_frame(const uint8_t *frame, size_t len, const uint8_t our[6],
                       struct reac_identity_frag *frag, struct first_frag *first,
                       struct reac_identity *id)
{
	const uint8_t *blk = len >= REAC_CTRL_BLOCK_END ? frame + REAC_CTRL_BLOCK_OFF : NULL;
	struct reac_ctrl_parsed p;
	enum reac_ctrl_kind k = reac_ctrl_parse(frame, len, &p);
	int is_8819 = len >= 50 && frame[12] == 0x88 && frame[13] == 0x19;
	/* sum_ok: the frame has a whole control block and it sums to 0 mod 256.
	 * type_filler: the frame has a whole control block and type 00 00. */
	int sum_ok = len >= REAC_CTRL_BLOCK_END && block_sum_closes(frame);
	int type_filler = len >= REAC_CTRL_BLOCK_END && frame[16] == 0x00 && frame[17] == 0x00;
	/* NONE exactly for a frame under 50 B or not 0x8819.
	 * mutant: src/reac_ctrlblk.c:262 `AUDIO_OFF` -> `TYPE_OFF`
	 * input: breakages
	 * mutant: src/reac_ctrlblk.c:262 `frame[13] != 0x19` -> `frame[13] != 0x18`
	 * input: fixture-filler */
	if ((k == REAC_CTRL_NONE) == is_8819)
		abort();
	/* NULL out is allowed, and gives the same verdict.
	 * mutant: src/reac_ctrlblk.c:260 `out = &scratch;` -> `return REAC_CTRL_NONE;`
	 * input: fixture-filler */
	if (reac_ctrl_parse(frame, len, NULL) != k)
		abort();
	/* The verdict is the kind in out, and the kind has a name.
	 * mutant: src/reac_ctrlblk.c:280 `return out->kind;` -> `return REAC_CTRL_LINK2;`
	 * input: fixture-filler
	 * mutant: src/reac_ctrlblk.c:223 `"filler"` -> `NULL`
	 * input: fixture-filler
	 * mutant: src/reac_ctrlblk.c:223 `"filler"` -> `"?"`
	 * input: fixture-filler */
	if (k != p.kind || !reac_ctrl_kind_name(k) || strcmp(reac_ctrl_kind_name(k), "?") == 0)
		abort();

	uint16_t addr = 0;
	const uint8_t *pl = NULL;
	size_t pll = 0;
	int r = reac_ctrl_identity_reply(frame, len, &addr, &pl, &pll);
	/* identity_reply returns -1 only for a NULL argument, and none is passed.
	 * mutant: src/reac_ctrlblk.c:352 `return 0;` -> `return -2;`
	 * input: fixture-filler */
	if (r < 0)
		abort();
	if (r == 1) {
		/* A reply comes only from a frame whose block checksum closes, and its
		 * payload, record checksum and f7 are inside the frame.
		 * mutant: src/reac_ctrlblk.c:370 `!= 0` -> `< -1`
		 * input: breakages
		 * mutant: src/reac_ctrlblk.c:376 `- 13` -> `+ 4096`
		 * input: identity-reply-s1608-firmware */
		if (!sum_ok || !inside(pl, pll + 2, frame, len))
			abort();
		/* The payload starts at block[20], and the SysEx length block[8] is the
		 * payload and 13 bytes of framing.
		 * mutant: src/reac_ctrlblk.c:375 `&block[20]` -> `&block[21]`
		 * input: identity-reply-s1608-firmware
		 * mutant: src/reac_ctrlblk.c:376 `- 13` -> `- 12`
		 * input: identity-reply-s1608-firmware */
		if (pl != blk + 20 || pll + 13 != blk[8])
			abort();
		/* The record TAG(2) ADDR(2) PAYLOAD CKSUM sums to 0 mod 128.
		 * mutant: src/reac_ctrlblk.c:73 `((s & 0x7f) == 0) ? 0 : -1` -> `0`
		 * input: reply-inner-checksum
		 * mutant: src/reac_ctrlblk.c:372 `!= 0` -> `< -1`
		 * input: breakages */
		if (!record_sum_closes(blk + 16, pll + 5))
			abort();
		/* The address is the record's own, block[18] high and block[19] low: it
		 * picks the identity field that the payload fills.
		 * contract: include/reac/reac_ctrlblk.h:600-601 (addr_lo is the low half
		 * of the Roland address); reac.ksy:1834-1839 (addr_lo, u2be, after TAG
		 * 0x0500), :1714-1724 (the tag is the high half and addr_lo the low)
		 * mutant: src/reac_ctrlblk.c:374 `| block[19]` -> ``
		 * input: identity-reply-addr-0011 */
		if (addr != (uint16_t)(blk[18] << 8 | blk[19]))
			abort();
		/* ingest returns -1 only for a NULL argument.
		 * mutant: src/reac_identity.c:68 `if (!id || (len > 0 && !payload))` -> `if (id)`
		 * input: identity-reply-s1608-firmware */
		if (reac_identity_ingest(id, addr, pl, pll) < 0)
			abort();
	}

	struct reac_identity_frag before;
	memcpy(&before, frag, sizeof before);
	r = reac_ctrl_identity_fragment(frag, frame, len, &addr, &pl, &pll);
	/* identity_fragment returns -1 only for a NULL argument.
	 * mutant: src/reac_ctrlblk.c:1363 `return 0;` -> `return -2;`
	 * input: fixture-filler */
	if (r < 0)
		abort();
	/* A frame whose block checksum does not close is corrupt: it neither opens
	 * nor closes a record, so the reassembly state does not change.
	 * mutant: src/reac_ctrlblk.c:1369 `!= 0` -> `< -1`
	 * input: breakages */
	if (!sum_ok && memcmp(&before, frag, sizeof before) != 0)
		abort();
	if (r == 1) {
		/* The payload, record checksum and f7 are inside the buffer.
		 * mutant: src/reac_ctrlblk.c:1396 `&r[11]` -> `&r[60]`
		 * input: fixtures-all */
		if (!inside(pl, pll + 2, frag->buf, sizeof frag->buf))
			abort();
		/* The payload starts after f0 41 dev 00 00 12 12 05 00 addr(2).
		 * mutant: src/reac_ctrlblk.c:1396 `&r[11]` -> `&r[12]`
		 * input: fixtures-all */
		if (pl != frag->buf + 11)
			abort();
		/* The reassembled record TAG(2) ADDR(2) PAYLOAD CKSUM sums to 0 mod 128.
		 * mutant: src/reac_ctrlblk.c:73 `((s & 0x7f) == 0) ? 0 : -1` -> `0`
		 * input: frag-inner-checksum
		 * mutant: src/reac_ctrlblk.c:1393 `!= 0` -> `< -1`
		 * input: breakages */
		if (!record_sum_closes(frag->buf + 7, pll + 5))
			abort();
		/* The address is bytes 9 and 10 of the record that the FIRST and the
		 * LAST join, read by the harness from the two frames: a FIRST body
		 * shorter than 11 bytes leaves one or both to the LAST.
		 * contract: reac.ksy:1905-1920 (the FIRST and LAST bodies, joined, are one
		 * SysEx: f0 41 0a 00 00 12 12 05 00, then addr_lo);
		 * include/reac/reac_ctrlblk.h:620-628 (the joined SysEx is a DT1 on tag 0x0500)
		 * mutant: src/reac_ctrlblk.c:1395 `| r[10]` -> ``
		 * input: frag-addr-1011
		 * mutant: src/reac_ctrlblk.c:1374 `f->len = (uint8_t)n;` -> `f->len = (uint8_t)(n + 1);`
		 * input: frag-first-10-addr-1011 */
		if (!first->have || addr != (uint16_t)(joined_byte(first, blk, 9) << 8 |
		                                       joined_byte(first, blk, 10)))
			abort();
		/* ingest returns -1 only for a NULL argument.
		 * mutant: src/reac_identity.c:68 `if (!id || (len > 0 && !payload))` -> `if (id)`
		 * input: fixtures-all */
		if (reac_identity_ingest(id, addr, pl, pll) < 0)
			abort();
	}
	if (opens_record(frame, len, sum_ok)) {
		first->have = 1;
		first->n = blk[8];
		memcpy(first->body, blk + 9, blk[8]);
	}

	if (is_8819) {
		/* The addresses and the counter come from the frame.
		 * mutant: src/reac_ctrlblk.c:266 `frame, 6` -> `frame + 1, 6`
		 * input: fixture-filler
		 * mutant: src/reac_ctrlblk.c:267 `frame + 6, 6` -> `frame + 7, 6`
		 * input: fixture-filler
		 * mutant: src/reac_ctrlblk.c:269 `frame[CNT_OFF] |` -> `(frame[CNT_OFF] ^ 1) |`
		 * input: fixture-filler */
		if (memcmp(p.dst, frame, 6) || memcmp(p.src, frame + 6, 6) ||
		    p.counter != (uint16_t)(frame[14] | frame[15] << 8))
			abort();
		/* FILLER is type 00 00, and only that type.
		 * mutant: src/reac_ctrlblk.c:278 `t0 == 0x00 && t1 == 0x00` -> `t0 == 0x00`
		 * input: box-hb-type-0001-bad-checksum
		 * mutant: src/reac_ctrlblk.c:278 `t1 == 0x00` -> `t1 == 0x01`
		 * input: fixture-filler */
		if ((k == REAC_CTRL_FILLER) != (frame[16] == 0x00 && frame[17] == 0x00))
			abort();
		/* checksum_verify is 0 exactly when the block sums to 0 mod 256.
		 * mutant: src/reac_ctrlblk.c:51 `(s & 0xff) == 0 ? 0 : -1` -> `0`
		 * input: breakages
		 * mutant: src/reac_ctrlblk.c:51 `(s & 0xff) == 0 ? 0 : -1` -> `-1`
		 * input: fixture-l1-box-hb */
		if (reac_ctrl_checksum_verify(frame) != (sum_ok ? 0 : -1))
			abort();
		/* A head-amp record is only ever a link-4 SINGLE. The harness reads the
		 * link and the segment from the frame, block[0] and block[1], and not from
		 * the parser's fields.
		 * contract: include/reac/reac_ctrlblk.h:88, :93 (REAC_LINK_RECORD,
		 * REAC_SEG_SINGLE), :312-313 (HEADAMP is link 4, SINGLE), :348-349 (link is
		 * block[0], seg is block[1])
		 * mutant: src/reac_ctrlblk.c:306 `REAC_CTRL_LINK2` -> `REAC_CTRL_HEADAMP`
		 * input: breakages
		 * mutant: src/reac_ctrlblk.c:314 `REAC_CTRL_RECORD_FRAGMENT` -> `REAC_CTRL_HEADAMP`
		 * input: fixture-frag-first
		 * mutant: src/reac_ctrlblk.c:272 `block[0];` -> `block[0] ? block[0] : REAC_LINK_RECORD;`
		 * input: headamp-link-0 */
		if (k == REAC_CTRL_HEADAMP && (frame[REAC_CTRL_BLOCK_OFF] != REAC_LINK_RECORD ||
		                               frame[REAC_CTRL_BLOCK_OFF + 1] != REAC_SEG_SINGLE))
			abort();
		int want_v = -1;
		if (frame[18] == REAC_LINK_RECORD && frame[19] == REAC_SEG_SINGLE)
			want_v = record_sum_closes(frame + 34, 6) ? 0 : -1;
		/* The record check refuses anything but a link-4 SINGLE, whatever its bytes
		 * sum to, and on a link-4 SINGLE it is 0 exactly when the six record bytes
		 * frame[34..40) sum to 0 mod 128.
		 * mutant: src/reac_ctrlblk.c:73 `((s & 0x7f) == 0) ? 0 : -1` -> `0`
		 * input: breakages
		 * mutant: src/reac_ctrlblk.c:1319 `frame[REAC_CTRL_BLOCK_OFF] != REAC_LINK_RECORD` -> `0`
		 * input: fixture-l1-box-hb
		 * mutant: src/reac_ctrlblk.c:1322 `HEADAMP_REC_OFF` -> `HEADAMP_REC_OFF + 1`
		 * input: fixture-l4-headamp */
		if (reac_ctrl_headamp_record_verify(frame) != want_v)
			abort();
		check_ports(blk);
	}

	struct reac_ctrl_parsed q;
	enum reac_master_rx_event ev = (enum reac_master_rx_event)-1;
	if (reac_ctrl_classify_box_frame(frame, len, our, &q, &ev) == 0) {
		/* Only a Roland-OUI source that is not us.
		 * mutant: src/reac_ctrl.c:20 `return -1;` -> `;`
		 * input: breakages
		 * mutant: src/reac_ctrl.c:21 `== 0` -> `== 7`
		 * input: own-echo-join */
		if (q.src[0] != 0x00 || q.src[1] != 0x40 || q.src[2] != 0xab ||
		    memcmp(q.src, our, 6) == 0)
			abort();
		/* Outside FILLER (type 00 00), only a frame whose block sums to 0 mod 256.
		 * mutant: src/reac_ctrl.c:29 `!= 0` -> `< -1`
		 * input: breakages
		 * mutant: src/reac_ctrl.c:29 `REAC_CTRL_FILLER` -> `REAC_CTRL_BOX_HB`
		 * input: breakages */
		if (!type_filler && !sum_ok)
			abort();
		/* The event is one of the six.
		 * mutant: src/reac_ctrl.c:95 `REAC_M_RX_BOX_UNICAST` -> `(enum reac_master_rx_event)9`
		 * input: fixture-filler
		 * mutant: src/reac_ctrl.c:95 `*ev = REAC_M_RX_BOX_UNICAST;` -> ``
		 * input: fixture-filler */
		if ((int)ev < REAC_M_RX_BOX_BCAST_FILLER || ev > REAC_M_RX_BOX_CONFIG)
			abort();
	}

	const struct reac_box_model *want_m = NULL;
	if (k == REAC_CTRL_CONFIG_ANNOUNCE && frame[16] == 0xcd && frame[17] == 0xea)
		want_m = row_of_block(blk);
	/* Only a cdea config-announce names a row, and the row is the first one whose
	 * declaration, as the harness builds it (declaration_of), is the frame's block.
	 * contract: include/reac/reac_ctrlblk.h:432-434, :539-541 (the entry a config
	 * announce is byte-equal to)
	 * mutant: src/reac_box_synth.c:105 `out[5] = 0x00;` -> `out[5] = 0x01;`
	 * input: fixture-l1-decl-84
	 * mutant: src/reac_ctrlblk.c:720 `return &t[i];` -> `return &t[0];`
	 * input: fixture-l1-decl-84
	 * mutant: src/reac_ctrlblk.c:707 `return NULL;` -> `return reac_box_catalogue(NULL);`
	 * input: fixture-l1-box-hb
	 * mutant: src/reac_ctrlblk.c:722 `return NULL;` -> `return t;`
	 * input: breakages */
	if (reac_box_catalogue_match(frame, len) != want_m)
		abort();
}

/* Build a row's blocks and read them back through the parsers. */
static void round_trip(const struct reac_box_model *m, const uint8_t our[6], uint16_t counter)
{
	static const uint8_t box[6] = { 0x00, 0x40, 0xab, 0x00, 0x00, 0x01 };
	uint8_t out[REAC_FRAME_BYTES];
	struct reac_identity id;
	struct reac_identity_frag frag;
	reac_identity_init(&id);
	memset(&frag, 0, sizeof frag);

	for (int b = REAC_BOX_BLOCK_CONFIG; b <= REAC_BOX_BLOCK_IDENT_LAST; b++) {
		size_t n = reac_ctrl_build_as(out, m, (enum reac_box_block)b, our, box, counter,
		                              NULL, 0);
		if (n == 0)
			continue;
		/* A builder only emits a legal geometry. (The n > sizeof out term has no
		 * record: a builder that makes n too large writes past out before here.)
		 * mutant: src/reac_ctrlblk.c:383 `+ 2;` -> `+ 3;`
		 * input: round-trip-s1608 */
		if (n > sizeof out || reac_frame_channels(n) == 0)
			abort();
		uint8_t *frame = fuzz_dup(out, n);
		struct reac_ctrl_parsed p;
		enum reac_ctrl_kind k = reac_ctrl_parse(frame, n, &p);
		uint16_t addr;
		const uint8_t *pl;
		size_t pll;
		switch (b) {
		case REAC_BOX_BLOCK_CONFIG: {
			struct reac_box_ports ports;
			/* The declaration is a config-announce whose block sums to 0, names
			 * this row, and declares this row's widths.
			 * mutant: src/reac_ctrlblk.c:250 `return REAC_CTRL_CONFIG_ANNOUNCE;` -> `return REAC_CTRL_BOX_HB;`
			 * input: round-trip-s1608
			 * mutant: src/reac_ctrlblk.c:38 `256 - (s & 0xff)` -> `255 - (s & 0xff)`
			 * input: round-trip-s1608
			 * mutant: src/reac_ctrlblk.c:720 `return &t[i];` -> `return &t[0];`
			 * input: round-trip-s0808
			 * mutant: src/reac_ports.c:17 `REAC_SEG_SINGLE` -> `REAC_SEG_FIRST`
			 * input: round-trip-s1608
			 * mutant: src/reac_ports.c:40 `= in_slots` -> `= out_slots`
			 * input: round-trip-s1608
			 * mutant: src/reac_ports.c:41 `= out_slots` -> `= in_slots`
			 * input: round-trip-s1608 */
			if (k != REAC_CTRL_CONFIG_ANNOUNCE ||
			    !block_sum_closes(frame) ||
			    reac_box_catalogue_match(frame, n) != m ||
			    reac_ports_parse(frame + REAC_CTRL_BLOCK_OFF, &ports) != 0 ||
			    ports.in_ch != m->in_ch || ports.out_ch != m->out_ch)
				abort();
			uint8_t want[REAC_CTRL_BLOCK_LEN];
			/* The block the builder sent is the row's declaration, as the harness
			 * builds it (declaration_of).
			 * contract: include/reac/reac_ctrlblk.h:432-434, :448-454, :485
			 * mutant: src/reac_box_synth.c:105 `out[5] = 0x00;` -> `out[5] = 0x01;`
			 * input: round-trip-s1608 */
			if (!declaration_of(m, want) ||
			    memcmp(frame + REAC_CTRL_BLOCK_OFF, want, sizeof want) != 0)
				abort();
			break;
		}
		case REAC_BOX_BLOCK_CC0016:
		case REAC_BOX_BLOCK_CC001A:
			/* A firmware or REAC-version record is a GRANT that reads back as
			 * one identity reply, and ingest takes it.
			 * mutant: src/reac_ctrlblk.c:325 `REAC_DT1_TAG_HEADAMP` -> `REAC_DT1_TAG_IDENTITY`
			 * input: round-trip-s1608
			 * mutant: src/reac_ctrlblk.c:353 `p.dt1_tag != REAC_DT1_TAG_IDENTITY` -> `p.dt1_tag == REAC_DT1_TAG_IDENTITY`
			 * input: round-trip-s1608
			 * mutant: src/reac_identity.c:78 `return 1;` -> `return 0;`
			 * input: round-trip-s1608 */
			if (k != REAC_CTRL_GRANT ||
			    reac_ctrl_identity_reply(frame, n, &addr, &pl, &pll) != 1 ||
			    reac_identity_ingest(&id, addr, pl, pll) != 1)
				abort();
			break;
		case REAC_BOX_BLOCK_IDENT_FIRST:
			/* The FIRST fragment is a fragment, and it is kept, not closed.
			 * mutant: src/reac_ctrlblk.c:314 `REAC_CTRL_RECORD_FRAGMENT` -> `REAC_CTRL_GRANT`
			 * input: round-trip-s0808
			 * mutant: src/reac_ctrlblk.c:1376 `return 0;` -> `return 1;`
			 * input: round-trip-s0808 */
			if (k != REAC_CTRL_RECORD_FRAGMENT ||
			    reac_ctrl_identity_fragment(&frag, frame, n, &addr, &pl, &pll) != 0)
				abort();
			break;
		case REAC_BOX_BLOCK_IDENT_LAST:
			/* The LAST fragment closes the record, and ingest takes it.
			 * mutant: src/reac_ctrlblk.c:309 `out->seg != REAC_SEG_SINGLE` -> `out->seg == REAC_SEG_FIRST`
			 * input: round-trip-s0808
			 * mutant: src/reac_ctrlblk.c:1398 `return 1;` -> `return 0;`
			 * input: round-trip-s0808
			 * mutant: src/reac_identity.c:55 `return 1;` -> `return 0;`
			 * input: round-trip-s0808 */
			if (k != REAC_CTRL_RECORD_FRAGMENT ||
			    reac_ctrl_identity_fragment(&frag, frame, n, &addr, &pl, &pll) != 1 ||
			    reac_identity_ingest(&id, addr, pl, pll) != 1)
				abort();
			break;
		default:
			/* CC0014 and CC0013 are GRANTs whose block sums to 0 mod 256. CC0013 is
			 * sent raw, so its stored bytes must already close.
			 * mutant: src/reac_ctrlblk.c:331 `REAC_CTRL_GRANT` -> `REAC_CTRL_LINK2`
			 * input: round-trip-s1608
			 * mutant: src/reac_box_synth.c:86 `0x7a` -> `0x7b`
			 * input: round-trip-s1608 */
			if (k != REAC_CTRL_GRANT || !block_sum_closes(frame))
				abort();
			break;
		}
		free(frame);
	}
	/* The identity page the row emitted is the row's own facts.
	 * mutant: src/reac_identity.c:77 `id->has_fw = 1;` -> `id->has_fw = 0;`
	 * input: round-trip-s1608
	 * mutant: src/reac_identity.c:30 `+ p[3]` -> `+ p[3] + 1`
	 * input: round-trip-s1608
	 * mutant: src/reac_identity.c:89 `id->has_reac_version = 1;` -> `id->has_reac_version = 0;`
	 * input: round-trip-s1608
	 * mutant: src/reac_identity.c:86 `payload + 2` -> `payload + 4`
	 * input: round-trip-s1608
	 * mutant: src/reac_identity.c:87 `payload + 4` -> `payload + 6`
	 * input: round-trip-s1608
	 * mutant: src/reac_identity.c:88 `payload + 6` -> `payload + 4`
	 * input: round-trip-s1608 */
	if (!id.has_fw || id.fw_milli != m->fw_milli || !id.has_reac_version ||
	    id.reac_version_major != m->reac_major || id.reac_version_minor != m->reac_minor ||
	    id.reac_version_patch != m->reac_patch)
		abort();
	/* A row that sends a name record gets its own name back. (A row with a NULL
	 * name sends an empty name, which ingest refuses at IDENT_LAST above.)
	 * mutant: src/reac_identity.c:54 `id->has_model_name = 1;` -> `id->has_model_name = 0;`
	 * input: round-trip-s0808
	 * mutant: src/reac_identity.c:49 `(char)p[1 + i]` -> `(char)(p[1 + i] ^ 1)`
	 * input: round-trip-s0808 */
	if (m->has_identity_record &&
	    (!id.has_model_name || strcmp(id.model_name, m->name ? m->name : "") != 0))
		abort();
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	if (size >= FUZZ_INPUT_MAX)
		return 0;
	struct fuzz_in in = fuzz_in(data, size);
	uint8_t our[6];
	for (int i = 0; i < 6; i++)
		our[i] = fuzz_u8(&in);
	uint8_t mode = fuzz_u8(&in);

	if (mode & 1) {
		size_t count = 0;
		const struct reac_box_model *cat = reac_box_catalogue(&count);
		/* The catalogue is not empty.
		 * mutant: src/reac_ctrlblk.c:663 `sizeof(BOX_CATALOGUE) / sizeof(BOX_CATALOGUE[0])` -> `0`
		 * input: round-trip-s1608
		 * mutant: src/reac_ctrlblk.c:664 `return BOX_CATALOGUE;` -> `return NULL;`
		 * input: round-trip-s1608 */
		if (!cat || count == 0)
			abort();
		round_trip(&cat[(size_t)(mode >> 1) % count], our, 0x1234);
	}

	struct reac_identity id;
	struct reac_identity_frag frag;
	struct first_frag first = { 0 };
	reac_identity_init(&id);
	memset(&frag, 0, sizeof frag);

	/* The documented refusals of a bad argument, which no frame can reach. */
	{
		uint16_t a;
		const uint8_t *pl;
		size_t n;
		uint8_t code = 0xee, blk[32] = { 0 };
		/* mutant: src/reac_ctrlblk.c:349 `return -1;` -> `return 0;`
		 * input: fixture-filler
		 * mutant: src/reac_ctrlblk.c:1357 `return -1;` -> `return 0;`
		 * input: fixture-filler
		 * mutant: src/reac_ports.c:12 `return -1;` -> `return 0;`
		 * input: fixture-filler
		 * mutant: src/reac_ports.c:11 `if (!block || !out)` -> `if (!out) return block ? -1 : 0; if (0)`
		 * input: fixture-filler
		 * mutant: src/reac_ports.c:54 `return -1;` -> `return 0;`
		 * input: fixture-filler
		 * mutant: src/reac_ports.c:52 `*first_code = 0;` -> `*first_code = 1;`
		 * input: fixture-filler
		 * mutant: src/reac_ctrlblk.c:235 `return "?";` -> `return "!";`
		 * input: fixture-filler */
		if (reac_ctrl_identity_reply(NULL, 0, &a, &pl, &n) != -1 ||
		    reac_ctrl_identity_fragment(&frag, NULL, 0, &a, &pl, &n) != -1 ||
		    reac_ports_parse(blk, NULL) != -1 || reac_ports_parse(NULL, NULL) != -1 ||
		    reac_ports_unknown(NULL, &code) != -1 || code != 0 ||
		    strcmp(reac_ctrl_kind_name((enum reac_ctrl_kind)(REAC_CTRL_UNKNOWN_CTRL + 1)),
		           "?") != 0)
			abort();
	}

	for (int i = 0; i < MAX_FRAMES && in.n; i++) {
		const uint8_t *body;
		size_t len = fuzz_record(&in, &body);
		uint8_t *frame = fuzz_dup(body, len);
		fuzz_frame(frame, len, our, &frag, &first, &id);
		free(frame);
	}
	/* Whatever was ingested is a well-formed string.
	 * mutant: src/reac_identity.c:53 `id->model_name[w] = '\0';` -> `memset(id->model_name, 'A', sizeof id->model_name);`
	 * input: fixtures-all */
	if (id.has_model_name && memchr(id.model_name, 0, sizeof id.model_name) == NULL)
		abort();
	return 0;
}
