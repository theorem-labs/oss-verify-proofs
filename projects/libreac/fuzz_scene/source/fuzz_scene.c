// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>
// Modified by Theorem Labs, 2026-10-25: a modified copy of fuzz/fuzz_scene.c at libreac 9ed322ef.

/* libFuzzer harness: the SCENE PUSH framing (reac_ctrl_build_scene_step,
 * reac_ctrl_scene_set_mac, reac_ctrl_scene_build in src/reac_ctrlblk.c) over a
 * scene body (src/reac_scene_body.c holds the one libreac ships).
 *
 * The scene body is the largest object libreac puts on the wire, and the framing
 * is the only code that indexes into it: 8904 bytes cut into a 24-byte FIRST
 * chunk, 341 MIDDLE chunks of 26 and a 14-byte LAST one. The harness hands the
 * framing a body of any length and any step index, so its two guards are what
 * stands between a caller's mistake and a read past the body.
 *
 * Input:  [0]     flags: bit 0 = the body is REAC_SCENE_BYTES long whatever [1..2]
 *                 says; bit 1 = also run the whole transfer and reassemble it
 *         [1..2]  u16 LE body length (when bit 0 is clear)
 *         [3..4]  s16 LE step index
 *         [5..10] the MAC to substitute
 *         [11..]  bytes XORed over reac_scene_placeholder from offset 0, so the
 *                 body starts as the real one and drifts from it
 *
 * The body is its own allocation of exactly its length (of 1 byte when the
 * length is 0, so that it is never NULL).
 *
 * Properties, each an abort():
 *   - each door accepts exactly a REAC_SCENE_BYTES body (and the step builder
 *     exactly a step in [0, REAC_SCENE_STEPS)), and refuses everything else;
 *     a refused call writes nothing (not the block, not the body);
 *   - a built step is a cd ea link-1 bulk block whose 32 bytes sum to zero and
 *     whose payload is the body's bytes at that step's offset; the LAST step
 *     carries the fixed 12-byte trailer after its payload;
 *   - THE TRANSFER CARRIES THE BODY: the payload lengths every step declares sum to
 *     the total the FIRST step declares, and the payloads concatenated in step
 *     order are the body, byte for byte; reac_ctrl_parse reads every step back as
 *     SCENE_TRANSFER in the segment state it was built with;
 *   - set_mac writes the MAC at REAC_SCENE_MAC_OFF and nothing else; scene_build
 *     makes the body zeros, the three tags the box validates and the MAC, and
 *     nothing else.
 *
 * Each property's comment records a mutant (a one-line change that makes the
 * library wrong on purpose) and a seed in fuzz_scene_seed_corpus.zip that the
 * property catches it on.
 */
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include <reac/reac_ctrlblk.h>
#include <reac/reac_scene_body.h>

#include "fuzz.h"

/* The 32-byte block of the [type|block] template, blk[2..33], sums to 0 mod 256.
 * contract: include/reac/reac_ctrlblk.h:46, :70 */
static int block_sums_to_zero(const uint8_t blk[34])
{
	unsigned s = 0;
	for (int i = 2; i < 34; i++)
		s += blk[i];
	return (s & 0xff) == 0;
}

/* Offset and length of the body bytes step `k` carries: 24, then 341 x 26, then 14.
 * contract: include/reac/reac_ctrlblk.h:141-146 */
static void step_slice(int k, size_t *off, size_t *n)
{
	if (k == 0) {
		*off = 0;
		*n = REAC_SCENE_HEAD_BYTES;
	} else if (k <= REAC_SCENE_CHUNKS) {
		*off = REAC_SCENE_HEAD_BYTES + (size_t)(k - 1) * REAC_SCENE_CHUNK_BYTES;
		*n = REAC_SCENE_CHUNK_BYTES;
	} else {
		*off = REAC_SCENE_BYTES - REAC_SCENE_TAIL_BYTES;
		*n = REAC_SCENE_TAIL_BYTES;
	}
}

static void check_step(const uint8_t blk[34], const uint8_t *body, int k)
{
	/* type word cd ea, link 1, opcode 0x00 (bulk), block checksum closed
	 * contract: reac.ksy `frame_type` (0xcdea: control); include/reac/reac_ctrlblk.h:66-70
	 * (block[0] LINK, block[1] SEGMENT, block[2:4] LENGTH BE, block[4] OPCODE, at
	 * template offsets 2, 3, 4-5 and 6), :96 (REAC_OP_BULK), :126 (all three are link 1,
	 * opcode 0x00)
	 * mutant: src/reac_ctrlblk.c:107 `0xcd` -> `0xce`
	 * input: placeholder-step-0
	 * mutant: src/reac_ctrlblk.c:107 `0xea` -> `0xeb`
	 * input: placeholder-step-0
	 * mutant: src/reac_ctrlblk.c:110 `REAC_LINK_CTRL` -> `REAC_LINK_SECOND`
	 * input: placeholder-step-0
	 * mutant: src/reac_ctrlblk.c:112 `REAC_OP_BULK` -> `REAC_OP_SLOT_MAP`
	 * input: placeholder-step-0
	 * mutant: src/reac_ctrlblk.c:150 `reac_ctrl_block_cksum_stamp(blk + 2);` -> ``
	 * input: placeholder-step-0 */
	if (blk[0] != 0xcd || blk[1] != 0xea || blk[2] != REAC_LINK_CTRL ||
	    blk[6] != REAC_OP_BULK || !block_sums_to_zero(blk))
		abort();
	uint8_t seg = k == 0 ? REAC_SEG_FIRST : k <= REAC_SCENE_CHUNKS ? REAC_SEG_MIDDLE
	                                                               : REAC_SEG_LAST;
	/* the segment byte is FIRST, MIDDLE or LAST for this step
	 * mutant: src/reac_ctrlblk.c:111 `REAC_SEG_FIRST` -> `REAC_SEG_MIDDLE`
	 * input: placeholder-step-0
	 * mutant: src/reac_ctrlblk.c:141 `REAC_SEG_LAST` -> `REAC_SEG_MIDDLE`
	 * input: placeholder-step-342 */
	if (blk[3] != seg)
		abort();
	size_t off, n;
	step_slice(k, &off, &n);
	/* the declared payload length is this step's share
	 * mutant: src/reac_ctrlblk.c:125 `REAC_SCENE_CHUNK_BYTES & 0xff` -> `(REAC_SCENE_CHUNK_BYTES - 1) & 0xff`
	 * input: placeholder-step-1 */
	if ((size_t)(blk[4] << 8 | blk[5]) != n)
		abort();
	const uint8_t *pay = blk + (k == 0 ? 9 : 7);
	/* the payload is the body's bytes at this step's offset: block[7] on FIRST,
	 * after the declared total, block[5] on MIDDLE and LAST
	 * contract: reac.ksy `scene_header_payload.body_head` (block[7:31]),
	 * `scene_chunk_payload.chunk` and `scene_final_payload.chunk` (block[5:])
	 * mutant: src/reac_ctrlblk.c:126 `body + off` -> `body + off + 1`
	 * input: placeholder-step-1 */
	if (memcmp(pay, body + off, n) != 0)
		abort();
	if (k == REAC_SCENE_STEPS - 1) {
		static const uint8_t trailer[12] = { 0x00, 0x00, 0x03, 0x00, 0x00, 0x00,
		                                     0x01, 0x00, 0x00, 0x00, 0x00, 0x00 };
		/* The LAST step fills the same 26-byte slot, and the 12 bytes after its
		 * 14-byte payload are the fixed trailer of the M-200i and M-300
		 * captures. With this check, every byte of every step is fixed by a
		 * check.
		 * contract: include/reac/reac_ctrlblk.h:148-154 (the LAST step's trailer)
		 * mutant: src/reac_ctrlblk.c:136 `0x03` -> `0x00`
		 * input: placeholder-step-342 */
		if (memcmp(blk + 7 + REAC_SCENE_TAIL_BYTES, trailer, sizeof trailer) != 0)
			abort();
	}

	uint8_t frame[50] = { 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00, 0x40, 0xab, 0, 0, 1,
	                      0x88, 0x19 };
	memcpy(frame + 16, blk, 34);
	struct reac_ctrl_parsed p;
	/* reac_ctrl_parse reads the step back, framed the way a master stamps it: the
	 * template at [16:50] of an 0x8819 frame, from any source to any address.
	 * contract: include/reac/reac_ctrlblk.h:38 (the block at [18:50]), :305
	 * (link 1, opcode 0x00 is SCENE_TRANSFER)
	 * mutant: src/reac_ctrlblk.c:244 `REAC_CTRL_SCENE_TRANSFER` -> `REAC_CTRL_UNKNOWN_CTRL`
	 * input: placeholder-step-0
	 * mutant: src/reac_ctrlblk.c:272 `block[0]` -> `block[2]`
	 * input: placeholder-step-1
	 * mutant: src/reac_ctrlblk.c:273 `block[1]` -> `block[0]`
	 * input: placeholder-step-1
	 * mutant: src/reac_ctrlblk.c:274 `block[2] << 8` -> `block[3] << 8`
	 * input: placeholder-step-0
	 * mutant: src/reac_ctrlblk.c:275 `block[4]` -> `block[3]`
	 * input: placeholder-step-0
	 * mutant: src/reac_ctrlblk.c:51 `? 0 : -1` -> `? -1 : -1`
	 * input: placeholder-step-0 */
	if (reac_ctrl_parse(frame, sizeof frame, &p) != REAC_CTRL_SCENE_TRANSFER ||
	    p.link != REAC_LINK_CTRL || p.seg != seg || p.opcode != REAC_OP_BULK ||
	    p.blk_len != n || reac_ctrl_checksum_verify(frame) != 0)
		abort();
}

static void whole_transfer(const uint8_t *body)
{
	uint8_t *again = malloc(REAC_SCENE_BYTES);
	/* not a property: an allocation failed */
	if (!again)
		abort();
	size_t got = 0, declared = 0;
	for (int k = 0; k < REAC_SCENE_STEPS; k++) {
		uint8_t blk[34];
		/* a whole body is accepted at every step 0..342
		 * mutant: src/reac_ctrlblk.c:103 `step >= REAC_SCENE_STEPS` -> `step >= REAC_SCENE_STEPS - 1`
		 * input: placeholder-whole-transfer */
		if (reac_ctrl_build_scene_step(blk, body, REAC_SCENE_BYTES, k) != 0)
			abort();
		size_t n = (size_t)(blk[4] << 8 | blk[5]);
		if (k == 0)
			declared = (size_t)(blk[7] << 8 | blk[8]);
		/* The declared lengths never run past the body. This runs before
		 * check_step, so a step that declares too much stops here.
		 * mutant: src/reac_ctrlblk.c:144 `REAC_SCENE_TAIL_BYTES & 0xff` -> `(REAC_SCENE_TAIL_BYTES + 1) & 0xff`
		 * input: placeholder-whole-transfer */
		if (got + n > REAC_SCENE_BYTES)
			abort();
		check_step(blk, body, k);
		memcpy(again + got, blk + (k == 0 ? 9 : 7), n);
		got += n;
	}
	/* The FIRST step declares the whole total, the payloads sum to it, and they
	 * are the body. (check_step already fixes each length and each payload, so
	 * a library change reaches the first term only.)
	 * contract: reac.ksy `scene_header_payload.scene_total_len` (block[5:7], BE,
	 * 0x22c8); include/reac/reac_ctrlblk.h:141
	 * mutant: src/reac_ctrlblk.c:116 `REAC_SCENE_BYTES & 0xff` -> `(REAC_SCENE_BYTES - 1) & 0xff`
	 * input: placeholder-whole-transfer */
	if (declared != REAC_SCENE_BYTES || got != REAC_SCENE_BYTES ||
	    memcmp(again, body, REAC_SCENE_BYTES) != 0)
		abort();
	free(again);
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	if (size >= FUZZ_INPUT_MAX)
		return 0;
	struct fuzz_in in = fuzz_in(data, size);
	uint8_t flags = fuzz_u8(&in);
	size_t n = fuzz_u16(&in);
	int step = (int16_t)fuzz_u16(&in);
	uint8_t mac[6];
	for (int i = 0; i < 6; i++)
		mac[i] = fuzz_u8(&in);
	if (flags & 1)
		n = REAC_SCENE_BYTES;

	uint8_t *body = malloc(n ? n : 1);
	/* not a property: an allocation failed */
	if (!body)
		abort();
	for (size_t i = 0; i < n; i++)
		body[i] = i < REAC_SCENE_BYTES ? reac_scene_placeholder[i] : 0;
	const uint8_t *x;
	size_t nx = fuzz_take(&in, in.n, &x);
	for (size_t i = 0; i < nx && i < n; i++)
		body[i] ^= x[i];

	const int whole = n == REAC_SCENE_BYTES;
	/* The block starts as a known pattern, so a refused call that writes it shows. */
	uint8_t blk[34];
	memset(blk, 0xa5, sizeof blk);
	int r = reac_ctrl_build_scene_step(blk, body, n, step);
	/* The step builder accepts exactly a whole body and a step in [0, 343).
	 * mutant: src/reac_ctrlblk.c:101 `n != REAC_SCENE_BYTES` -> `n < REAC_SCENE_HEAD_BYTES`
	 * input: short-body-8903
	 * (This is the change of fuzz/sabotage/scene.patch.)
	 * mutant: src/reac_ctrlblk.c:103 `step >= REAC_SCENE_STEPS` -> `step > REAC_SCENE_STEPS`
	 * input: placeholder-step-343 */
	if (r != ((whole && step >= 0 && step < REAC_SCENE_STEPS) ? 0 : -1))
		abort();
	if (r == 0) {
		check_step(blk, body, step);
	} else {
		int changed = 0;
		for (size_t i = 0; i < sizeof blk; i++)
			changed |= blk[i] != 0xa5;
		/* A refused step writes nothing into the block.
		 * mutant: src/reac_ctrlblk.c:102 `return -1;` -> `return (blk ? (blk[0] = 0) : 0), -1;`
		 * input: short-body-24 */
		if (changed)
			abort();
	}
	if (whole && (flags & 2))
		whole_transfer(body);

	/* A copy of the body before set_mac, never NULL (also for n = 0). */
	uint8_t *before = malloc(n ? n : 1);
	/* not a property: an allocation failed */
	if (!before)
		abort();
	memcpy(before, body, n);
	r = reac_ctrl_scene_set_mac(body, n, mac);
	/* set_mac accepts exactly a whole body.
	 * mutant: src/reac_ctrlblk.c:156 `n != REAC_SCENE_BYTES` -> `n < REAC_SCENE_BYTES`
	 * input: short-body-8905
	 * mutant: src/reac_ctrlblk.c:159 `return 0;` -> `return 1;`
	 * input: placeholder-step-0 */
	if (r != (whole ? 0 : -1))
		abort();
	if (r == 0) {
		/* the MAC is at REAC_SCENE_MAC_OFF, and the bytes before and after it
		 * did not change
		 * mutant: src/reac_ctrlblk.c:158 `mac, 6` -> `mac, 4`
		 * input: placeholder-step-0
		 * mutant: src/reac_ctrlblk.c:158 `body + REAC_SCENE_MAC_OFF` -> `body + REAC_SCENE_MAC_OFF + 1`
		 * input: placeholder-step-0 */
		if (memcmp(body + REAC_SCENE_MAC_OFF, mac, 6) != 0 ||
		    memcmp(body, before, REAC_SCENE_MAC_OFF) != 0 ||
		    memcmp(body + REAC_SCENE_MAC_OFF + 6, before + REAC_SCENE_MAC_OFF + 6,
		           n - REAC_SCENE_MAC_OFF - 6) != 0)
			abort();
	} else {
		/* a refused call writes nothing
		 * mutant: src/reac_ctrlblk.c:157 `return -1;` -> `return (body && n ? (body[0] = 0) : 0), -1;`
		 * input: short-body-24 */
		if (memcmp(body, before, n) != 0)
			abort();
	}

	r = reac_ctrl_scene_build(body, n, mac);
	/* scene_build accepts exactly a whole body.
	 * mutant: src/reac_ctrlblk.c:164 `n != REAC_SCENE_BYTES` -> `n < REAC_SCENE_BYTES`
	 * input: short-body-8905 */
	if (r != (whole ? 0 : -1))
		abort();
	if (r == 0) {
		uint8_t expect[REAC_SCENE_BYTES];
		memset(expect, 0, sizeof expect);
		memcpy(expect + REAC_SCENE_TAG_ID_OFF, "1234", 4);
		memcpy(expect + REAC_SCENE_TAG_SYSP_OFF, "SYSP", 4);
		memcpy(expect + REAC_SCENE_TAG_SCEN_OFF, "SCEN", 4);
		memcpy(expect + REAC_SCENE_MAC_OFF, mac, 6);
		/* The API (reac_ctrlblk.h): "Build a body from zeros, the three validated
		 * tags and mac". So the whole body is zeros, "1234" at 0x000, "SYSP" at
		 * 0x368, "SCEN" at 0x37c and the MAC at 0x340, and nothing else.
		 * contract: include/reac/reac_ctrlblk.h:161-163 (the tags and where they
		 * sit), :167 (the MAC), :195 (zeros, the tags and the MAC)
		 * mutant: src/reac_ctrlblk.c:167 `memset(body, 0, REAC_SCENE_BYTES);` -> ``
		 * input: placeholder-step-0
		 * mutant: src/reac_ctrlblk.c:168 `"1234"` -> `"1235"`
		 * input: placeholder-step-0
		 * mutant: src/reac_ctrlblk.c:169 `"SYSP"` -> `"SYSQ"`
		 * input: placeholder-step-0
		 * mutant: src/reac_ctrlblk.c:170 `"SCEN"` -> `"SCEM"`
		 * input: placeholder-step-0
		 * mutant: src/reac_ctrlblk.c:171 `6);` -> `5);`
		 * input: placeholder-step-0 */
		if (memcmp(body, expect, REAC_SCENE_BYTES) != 0)
			abort();
	} else {
		/* A refused scene_build writes nothing. The refused set_mac above wrote
		 * nothing too, so the body is still equal to `before`.
		 * mutant: src/reac_ctrlblk.c:165 `return -1;` -> `return (body && n ? (body[0] = 0) : 0), -1;`
		 * input: short-body-24 */
		if (memcmp(body, before, n) != 0)
			abort();
	}
	free(before);
	free(body);
	return 0;
}
