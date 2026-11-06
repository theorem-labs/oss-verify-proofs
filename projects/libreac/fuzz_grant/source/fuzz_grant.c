// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>
// Modified by Theorem Labs, 2026-10-25: a modified copy of fuzz/fuzz_grant.c at libreac 9ed322ef.

/* libFuzzer harness: THE GRANT (src/reac_grant.c) — where a box's announced head-amp
 * base and width become slots, and slots become the enrolment sweep — with the
 * head-amp table that supplies the sweep's values (src/reac_headamp_tx.c).
 *
 * The base and the width are wire facts: the box announces its strap and declares
 * its inputs, and the master admits or refuses them here. The harness hands the
 * grant any base and width, a head-amp table set from the input, and a sweep buffer
 * of an input-chosen size, in its own allocation of exactly that many rows (1 row
 * when the count is 0).
 *
 * Input:  [0..1] s16 LE base  [2] in_ch  [3] u8 rows in the sweep buffer (0..255,
 *         so a 40-wide sweep of 128 rows fits)
 *         [4] how many head-amp cells to set, then that many [ch][param][value]
 *         [..] a raw allocation [base][width] handed to the sweep builder as a
 *         caller would build one by hand, a scene replay [base][width], a u32 LE
 *         re-assert period, then the number of scheduler frames to run (u16 LE, at
 *         most 4096)
 *
 * Properties, each an abort():
 *   - a box is admitted exactly when its slots [base, base+width) are a positive
 *     width of at most REAC_GRANT_MAX_WIDTH inside the head-amp space (0..0x2f):
 *     REFUSED, never moved, and a refusal leaves the caller's allocation as it was;
 *   - a sweep is REAC_GRANT_SWEEP_LEN(width) rows, refused when the buffer is
 *     smaller, and every row is a cd ea link-4 SINGLE whose block sums to zero;
 *   - its two head frames are the measured HEAD_ACK (row 0) and HEAD_MARK (row 4),
 *     byte for byte;
 *   - its group-A rows are, in the measured order, one head-amp record per
 *     allocated channel per parameter, each parsed back by reac_ctrl_parse as
 *     HEADAMP for that channel, parameter and the table's effective value, with
 *     its inner record checksum closed;
 *   - its group-B rows are the identity poll, byte for byte, and each is the RQ1
 *     (marker 12 11, TAG 05 00) for the address and size reac_ctrlblk.h names, in
 *     its order;
 *   - an unset cell carries the enrolling default that reac_headamp_tx.h states:
 *     phantom off, pad off, and a SENS that is not zero;
 *   - the head-amp scheduler only ever emits a channel, parameter and value the
 *     table can hold; the value is the table's effective value for that cell, and
 *     the cell is one the input set or one inside the armed scene; an unset cell
 *     goes out at most once, because a re-assert sends the set cells only.
 */
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include <reac/reac_ctrlblk.h>
#include <reac/reac_grant.h>
#include <reac/reac_headamp_tx.h>
#include <reac/reac_slots.h>

#include "fuzz.h"

#define MAX_FRAMES 4096

/* The two head frames of the grant sweep, as the M-200 goldens show them
 * (cdea 04 03 0014; record 12 12 01 00 is the ACK of the box's join, record
 * 12 12 00 00 is the marker before group B). Copied from the measured bytes, so
 * the harness does not take them from the library it checks.
 * contract: include/reac/reac_ctrlblk.h:908-930 (the sweep's order and
 * REAC_GRANT_HEAD_ACK, REAC_GRANT_HEAD_MARK); reac.ksy `join_grant_data` (a master
 * sends 06 00 01 00) */
static const uint8_t HEAD_ACK[34] = {
	0xcd, 0xea, 0x04, 0x03, 0x00, 0x14, 0x00, 0x02, 0x00, 0xfe, 0x0f, 0xf0,
	0x41, 0x0a, 0x00, 0x00, 0x12, 0x12, 0x01, 0x00, 0x06, 0x00, 0x01, 0x00,
	0x78, 0xf7, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
};
static const uint8_t HEAD_MARK[34] = {
	0xcd, 0xea, 0x04, 0x03, 0x00, 0x14, 0x00, 0x02, 0x00, 0xfe, 0x0f, 0xf0,
	0x41, 0x0a, 0x00, 0x00, 0x12, 0x12, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00,
	0x7d, 0xf7, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
};

/* Group B's six identity-page RQ1s, each the address (high, low) and the size it
 * asks for, in the header's order.
 * contract: include/reac/reac_ctrlblk.h:611-613 */
static const uint8_t POLL[REAC_GRANT_GROUPB_LEN][3] = {
	{ 0x00, 0x00, 4 }, { 0x06, 0x00, 8 }, { 0x10, 0x00, 17 },
	{ 0x10, 0x11, 9 }, { 0x11, 0x00, 17 }, { 0x11, 0x11, 9 },
};

/* A legal head-amp value: SENS 0..REAC_HEADAMP_SENS_MAX, phantom and pad 0 or 1.
 * contract: include/reac/reac_headamp_tx.h:159-161, include/reac/reac_ctrlblk.h:273
 * (REAC_HEADAMP_SENS_MAX) */
static int value_ok(uint8_t param, uint8_t value)
{
	return param == REAC_HEADAMP_SENS ? value <= REAC_HEADAMP_SENS_MAX
	                                  : param < REAC_HEADAMP_NPARAMS && value <= 1;
}

static void check_row(const uint8_t row[34])
{
	unsigned s = 0;
	for (int i = 2; i < 34; i++)
		s += row[i];
	/* Each sweep row is a cd ea link-4 SINGLE, and its block [2..33] sums to 0.
	 * contract: reac.ksy `frame_type` (0xcdea: control); include/reac/reac_grant.h:4
	 * (the cdea 04 03 grant), include/reac/reac_ctrlblk.h:46, :66-70
	 * mutant: include/reac/reac_ctrlblk.h:925 `0xcd` -> `0xce`
	 * input: box-base0-w8
	 * mutant: include/reac/reac_ctrlblk.h:925 `0xea` -> `0xeb`
	 * input: box-base0-w8
	 * mutant: include/reac/reac_ctrlblk.h:925 `0x03` -> `0x02`
	 * input: box-base0-w8
	 * mutant: include/reac/reac_ctrlblk.h:927 `0x78` -> `0x79`
	 * input: box-base0-w8 */
	if (row[0] != 0xcd || row[1] != 0xea || row[2] != REAC_LINK_RECORD ||
	    row[3] != REAC_SEG_SINGLE || (s & 0xff) != 0)
		abort();
}

/* One group-A row, framed as a master stamps it and read back by the parser. */
static void check_groupa(const uint8_t row[34], uint8_t ch, uint8_t param,
                         const struct reac_headamp_tx *tx, uint8_t want)
{
	uint8_t frame[50] = { 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00, 0x40, 0xab, 0, 0, 1,
	                      0x88, 0x19 };
	memcpy(frame + 16, row, 34);
	struct reac_ctrl_parsed p;
	/* The row parses as HEADAMP for this channel, parameter and effective value,
	 * and its inner record and block checksums close. The value 0 for width 40
	 * is caught only because rows is a u8: a 40-wide sweep needs 128 rows.
	 * contract: include/reac/reac_ctrlblk.h:819-821 (group A: one head-amp record
	 * per allocated channel per parameter), include/reac/reac_grant.h:100-103 (the
	 * value is tx's cell when set, else the default)
	 * mutant: src/reac_ctrlblk.c:326 `REAC_CTRL_HEADAMP` -> `REAC_CTRL_GRANT`
	 * input: box-base0-w8
	 * mutant: src/reac_ctrlblk.c:1468 `base + c` -> `base + c - 1`
	 * input: box-base0-w8
	 * mutant: src/reac_ctrlblk.c:1462 `base, p, values[p]` -> `base, p ^ (p < 2), values[p]`
	 * input: box-base0-w8
	 * mutant: src/reac_grant.c:168 `reac_grant_headamp_value(tx, ch, p);` -> `w == REAC_GRANT_MAX_WIDTH ? 0 : reac_grant_headamp_value(tx, ch, p);`
	 * input: box-base0-w40-rows128
	 * mutant: src/reac_grant.c:168 `tx, ch, p` -> `tx, ch, 0`
	 * input: box-base0-w8
	 * mutant: src/reac_ctrlblk.c:73 `(s & 0x7f) == 0` -> `(s & 0x7f) == 1`
	 * input: box-base0-w8
	 * mutant: src/reac_ctrlblk.c:51 `(s & 0xff) == 0` -> `(s & 0xff) == 1`
	 * input: box-base0-w8 */
	if (reac_ctrl_parse(frame, sizeof frame, &p) != REAC_CTRL_HEADAMP || p.ch != ch ||
	    p.param != param || p.value != reac_headamp_tx_effective(tx, ch, param) ||
	    reac_ctrl_headamp_record_verify(frame) != 0 || reac_ctrl_checksum_verify(frame) != 0)
		abort();
	unsigned s = 0;
	for (int i = 34; i < 40; i++)
		s += frame[i];
	/* The record TAG..CKSUM, frame[34..39], sums to 0 mod 128, added here: the
	 * check above asks reac_ctrl_headamp_record_verify, the library's own reading.
	 * contract: include/reac/reac_ctrlblk.h:53-55 (the 7-bit DT1 sum), :105-108 (the
	 * record runs frame[34..39]). A record window that the builder and the verifier
	 * both read wrong keeps the check above true.
	 * mutant: src/reac_ctrlblk.c:811 `HEADAMP_REC_LEN  6` -> `HEADAMP_REC_LEN  7`
	 * input: box-base0-w8 */
	if ((s & 0x7f) != 0)
		abort();
	/* The row carries the value that the input last set for this cell, or, for a
	 * cell the input never set, the header's default. The harness keeps the
	 * value itself; the check above asks reac_headamp_tx_effective, which the
	 * sweep builder calls too.
	 * contract: include/reac/reac_grant.h:100-103 (the value is the cell's when
	 * set, else the default), include/reac/reac_headamp_tx.h:171-172 (the table
	 * gives back the value set)
	 * mutant: src/reac_headamp_tx.c:32 `t->value[ch][param] = value;` -> `memset(t->value, 0, sizeof t->value); t->value[ch][param] = value;`
	 * input: box-base0-w8 */
	if (p.value != want)
		abort();
}

/* The value a cell must carry: the one the input last set, else the default. The
 * check of the unset cells below holds the default to the header. */
static uint8_t want_of(uint8_t was_set[][REAC_HEADAMP_NPARAMS],
                       uint8_t set_to[][REAC_HEADAMP_NPARAMS], uint8_t ch, uint8_t param)
{
	return was_set[ch][param] ? set_to[ch][param] : reac_headamp_default(param);
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	if (size >= FUZZ_INPUT_MAX)
		return 0;
	struct fuzz_in in = fuzz_in(data, size);
	int base = (int16_t)fuzz_u16(&in);
	int in_ch = fuzz_u8(&in);
	int rows = fuzz_u8(&in);

	struct reac_headamp_tx *tx = malloc(sizeof *tx);
	/* not a property: malloc failed, so there is no table to test. */
	if (!tx)
		abort();
	reac_headamp_tx_init(tx);
	/* The cells the input set: the scheduler may emit these at any time. */
	uint8_t was_set[REAC_HEADAMP_MAX_CH][REAC_HEADAMP_NPARAMS];
	memset(was_set, 0, sizeof was_set);
	/* The value the input last set for each cell, kept by the harness. */
	uint8_t set_to[REAC_HEADAMP_MAX_CH][REAC_HEADAMP_NPARAMS];
	memset(set_to, 0, sizeof set_to);
	int nset = fuzz_u8(&in);
	for (int i = 0; i < nset; i++) {
		uint8_t ch = fuzz_u8(&in), param = fuzz_u8(&in), value = fuzz_u8(&in);
		int r = reac_headamp_tx_set(tx, ch, param, value);
		/* An unknown parameter has no value and no default.
		 * contract: include/reac/reac_headamp_tx.h:167-168, :173
		 * mutant: src/reac_headamp_tx.c:69 `return 0;` -> `return 1;`
		 * input: refused-cells
		 * mutant: src/reac_headamp_tx.c:61 `return 0;` -> `return 1;`
		 * input: refused-cells */
		if (param >= REAC_HEADAMP_NPARAMS &&
		    (reac_headamp_tx_effective(tx, ch, param) != 0 || reac_headamp_default(param) != 0))
			abort();
		/* A set is accepted exactly when the channel is in the table and the value
		 * is legal for the parameter.
		 * contract: include/reac/reac_headamp_tx.h:156-161
		 * mutant: src/reac_headamp_tx.c:19 `value <= 0x01` -> `value <= 0x02`
		 * input: refused-cells */
		if (r != ((ch < REAC_HEADAMP_MAX_CH && value_ok(param, value)) ? 0 : -1))
			abort();
		/* After an accepted set, the table gives back the value that was set.
		 * contract: include/reac/reac_headamp_tx.h:171-172
		 * mutant: src/reac_headamp_tx.c:32 `= value;` -> `= 0;`
		 * input: box-base0-w8 */
		if (r == 0 && reac_headamp_tx_effective(tx, ch, param) != value)
			abort();
		if (r == 0) {
			was_set[ch][param] = 1;
			set_to[ch][param] = value;
		}
	}

	for (int c = 0; c < REAC_HEADAMP_MAX_CH; c++)
		for (uint8_t p = 0; p < REAC_HEADAMP_NPARAMS; p++) {
			if (was_set[c][p])
				continue;
			uint8_t v = reac_headamp_tx_effective(tx, (uint8_t)c, p);
			uint8_t d = reac_headamp_default(p);
			/* An unset cell carries the enrolling default, and the default is what
			 * reac_headamp_tx.h:165-168 states: phantom off and pad off (+48 V
			 * into a ribbon mic can destroy it), SENS not zero (the box enrols
			 * only a channel armed with a real value). The expected values are
			 * the header's, not the library's.
			 * contract: include/reac/reac_headamp_tx.h:165-168, :171-174
			 * mutant: src/reac_headamp_tx.c:51 `0x00` -> `0x01`
			 * input: box-base0-w8
			 * mutant: src/reac_headamp_tx.c:52 `0x00` -> `0x01`
			 * input: box-base0-w8
			 * mutant: src/reac_headamp_tx.c:53 `0x20` -> `0x00`
			 * input: box-base0-w8
			 * mutant: src/reac_headamp_tx.c:74 `return reac_headamp_default(param);` -> `return 0;`
			 * input: box-base0-w8 */
			if (v != d || !value_ok(p, d) || (p == REAC_HEADAMP_SENS ? d == 0 : d != 0))
				abort();
		}

	const int fits = in_ch > 0 && in_ch <= REAC_GRANT_MAX_WIDTH && base >= 0 &&
	                 base + in_ch - 1 <= REAC_HEADAMP_CEILING;
	/* The library's fit test is the admission rule above. The first record is the
	 * change of fuzz/sabotage/grant.patch (last slot 0x30 admitted).
	 * contract: include/reac/reac_grant.h:43-47 (the head-amp space 0x00..0x2f, a
	 * hard ceiling), :60 (REAC_GRANT_MAX_WIDTH), :76-82 (fits = [base, base+width)
	 * inside that space); include/reac/reac_slots.h:63 (REAC_HEADAMP_CEILING)
	 * mutant: src/reac_grant.c:96 `REAC_HEADAMP_CEILING` -> `REAC_HEADAMP_CEILING + 1`
	 * input: box-base48-w1
	 * mutant: src/reac_grant.c:88 `width > REAC_GRANT_MAX_WIDTH` -> `width >= REAC_GRANT_MAX_WIDTH`
	 * input: box-base0-w40 */
	if (reac_grant_alloc_fits(base, in_ch) != fits)
		abort();
	struct reac_grant_alloc a = { 0, 0 };
	int r = reac_grant_allocate(&a, base, in_ch);
	/* A box is admitted exactly when it fits.
	 * mutant: src/reac_grant.c:108 `!reac_grant_alloc_fits(base, in_ch)` -> `0`
	 * input: box-base32-w32
	 * mutant: src/reac_grant.c:112 `return 0;` -> `return 1;`
	 * input: box-base0-w8 */
	if (r != (fits ? 0 : -1))
		abort();
	/* A refused box is not moved: reac_grant.h says that on -1 the allocation is
	 * not changed, so it keeps the zeros set above.
	 * contract: include/reac/reac_grant.h:84-85
	 * mutant: src/reac_grant.c:109 `return -1;` -> `return (out->base = 0, out->width = (uint8_t)in_ch, -1);`
	 * input: box-base32-w32
	 * mutant: src/reac_grant.c:109 `return -1;` -> `return (out->base = (uint8_t)base, -1);`
	 * input: box-base32-w32 */
	if (r != 0 && (a.base != 0 || a.width != 0))
		abort();
	/* An admitted box keeps the base and the width it asked for. It is then inside
	 * the head-amp space, because it fits (the check above).
	 * mutant: src/reac_grant.c:110 `(uint8_t)base` -> `0`
	 * input: box-base16-w24
	 * mutant: src/reac_grant.c:111 `(uint8_t)in_ch` -> `(uint8_t)(in_ch - 1)`
	 * input: box-base0-w8 */
	if (r == 0 && (a.base != base || a.width != in_ch))
		abort();

	if (r == 0) {
		uint8_t (*sweep)[34] = malloc((size_t)(rows > 0 ? rows : 1) * 34);
		/* not a property: malloc failed, so there is no sweep buffer to test. */
		if (!sweep)
			abort();
		int n = reac_grant_build_sweep(sweep, rows, &a, tx);
		int want = REAC_GRANT_SWEEP_LEN(a.width);
		/* The sweep has SWEEP_LEN(width) rows, and is refused when the buffer is
		 * smaller.
		 * contract: include/reac/reac_grant.h:62-65, :96-98
		 * mutant: src/reac_ctrlblk.c:1433 `max < n` -> `max <= n`
		 * input: box-base0-w40-rows128
		 * mutant: src/reac_ctrlblk.c:1474 `return k;` -> `return k + 1;`
		 * input: box-base0-w8 */
		if (n != (rows >= want ? want : -1))
			abort();
		if (n > 0) {
			for (int k = 0; k < n; k++)
				check_row(sweep[k]);
			/* Row 0 is HEAD_ACK and row 4 is HEAD_MARK, byte for byte. Both frames
			 * pass check_row, so only this check sees them swapped.
			 * mutant: src/reac_ctrlblk.c:1460 `GRANT_HEAD_ACK` -> `GRANT_HEAD_MARK`
			 * input: box-base0-w8
			 * mutant: src/reac_ctrlblk.c:1464 `GRANT_HEAD_MARK` -> `GRANT_HEAD_ACK`
			 * input: box-base0-w8 */
			if (memcmp(sweep[0], HEAD_ACK, 34) != 0 || memcmp(sweep[4], HEAD_MARK, 34) != 0)
				abort();
			/* HEAD_ACK | A[base].0..2 | HEAD_MARK | B x6 | A[base+1..].0..2
			 * contract: include/reac/reac_ctrlblk.h:908-914 (the sweep's order) */
			for (uint8_t p = 0; p < REAC_HEADAMP_NPARAMS; p++)
				check_groupa(sweep[1 + p], a.base, p, tx,
				             want_of(was_set, set_to, a.base, p));
			for (int c = 1; c < a.width; c++)
				for (uint8_t p = 0; p < REAC_HEADAMP_NPARAMS; p++)
					check_groupa(sweep[11 + (c - 1) * 3 + p],
					             (uint8_t)(a.base + c), p, tx,
					             want_of(was_set, set_to, (uint8_t)(a.base + c), p));
			for (int i = 0; i < REAC_GRANT_GROUPB_LEN; i++) {
				uint8_t poll[34];
				/* Group B is the identity poll, byte for byte.
				 * mutant: src/reac_ctrlblk.c:1466 `GRANT_GROUPB[i]` -> `GRANT_GROUPB[5 - i]`
				 * input: box-base0-w8
				 * mutant: src/reac_ctrlblk.c:1346 `i >= REAC_GRANT_GROUPB_LEN` -> `i >= REAC_GRANT_GROUPB_LEN - 1`
				 * input: box-base0-w8 */
				if (reac_ctrl_identity_poll_block(i, poll) != 0 ||
				    memcmp(poll, sweep[5 + i], 34) != 0)
					abort();
				/* And it polls the identity page the header names. The check above
				 * compares the sweep with reac_ctrl_identity_poll_block, which copies
				 * the same table, so a wrong table keeps it true: each group-B row is
				 * an RQ1 (marker 12 11) on TAG 05 00 for the i-th address and size,
				 * written out here.
				 * contract: include/reac/reac_ctrlblk.h:611-613 (0x0000 (4),
				 * 0x0600 (8), 0x1000 (17), 0x1011 (9), 0x1100 (17), 0x1111 (9)),
				 * include/reac/reac_grant.h:17 (marker 12 11, TAG 05 00)
				 * mutant: src/reac_ctrlblk.c:1336 `0x00, 0x00, 0x04, 0x77` -> `0x04, 0x00, 0x00, 0x77`
				 * input: box-base0-w8
				 * mutant: src/reac_ctrlblk.c:1338 `0x10, 0x00, 0x11, 0x5a` -> `0x10, 0x01, 0x10, 0x5a`
				 * input: box-base0-w8 */
				if (memcmp(sweep[5 + i] + 16, (const uint8_t[]){ 0x12, 0x11, 0x05, 0x00 }, 4) != 0 ||
				    memcmp(sweep[5 + i] + 20, POLL[i], 3) != 0)
					abort();
			}
		}
		free(sweep);
	}

	/* The builder judges an allocation it did not make: a hand-built one is admitted
	 * on the same terms as reac_grant_allocate's. */
	{
		struct reac_grant_alloc raw;
		raw.base = fuzz_u8(&in);
		raw.width = fuzz_u8(&in);
		uint8_t (*sweep)[34] = malloc((size_t)REAC_GRANT_SWEEP_MAX * 34);
		/* not a property: malloc failed, so there is no sweep buffer to test. */
		if (!sweep)
			abort();
		int n = reac_grant_build_sweep(sweep, REAC_GRANT_SWEEP_MAX, &raw, tx);
		/* A hand-built allocation gives SWEEP_LEN(width) rows exactly when it fits.
		 * mutant: src/reac_grant.c:170 `sweep, max,` -> `sweep, max - 1,`
		 * input: box-base0-w40 */
		if (n != (reac_grant_alloc_fits(raw.base, raw.width) ? REAC_GRANT_SWEEP_LEN(raw.width)
		                                                      : -1))
			abort();
		/* A NULL sweep or a NULL allocation is refused.
		 * mutant: src/reac_grant.c:153 `return -1;` -> `return 0;`
		 * input: box-base0-w8 */
		if (reac_grant_build_sweep(NULL, 1, &raw, tx) != -1 ||
		    reac_grant_build_sweep(sweep, REAC_GRANT_SWEEP_MAX, NULL, tx) != -1)
			abort();
		free(sweep);
	}

	uint8_t sb = fuzz_u8(&in), sw = fuzz_u8(&in);
	reac_headamp_tx_arm_scene(tx, sb, sw);
	reac_headamp_tx_set_resweep(tx, fuzz_u32(&in));
	int frames = fuzz_u16(&in) % (MAX_FRAMES + 1);
	/* How many times each unset cell went out. */
	uint8_t unset_sent[REAC_HEADAMP_MAX_CH][REAC_HEADAMP_NPARAMS];
	memset(unset_sent, 0, sizeof unset_sent);
	for (int i = 0; i < frames; i++) {
		uint8_t ch = 0xff, param = 0xff, value = 0xff;
		int e = reac_headamp_tx_next(tx, &ch, &param, &value);
		/* The scheduler answers 0 (nothing to send) or 1 (one record).
		 * mutant: src/reac_headamp_tx.c:127 `return 1;` -> `return 2;`
		 * input: box-base0-w8 */
		if (e != 0 && e != 1)
			abort();
		/* An emitted record has a channel in the table, a value that is legal for
		 * its parameter, and the table's effective value for that cell: the
		 * operator's value where set, the enrolling default where not. An edged
		 * cell is a set cell, so its value is the effective value too.
		 * contract: include/reac/reac_headamp_tx.h:171-174, :196-201
		 * mutant: src/reac_headamp_tx.c:154 `(uint8_t)c` -> `(uint8_t)(c + 8)`
		 * input: replay-past-ceiling
		 * mutant: src/reac_headamp_tx.c:125 `t->value[c][p]` -> `2`
		 * input: box-base0-w8
		 * mutant: src/reac_headamp_tx.c:156 `reac_headamp_tx_effective(t, (uint8_t)c, (uint8_t)p)` -> `0`
		 * input: replay-past-ceiling */
		if (e == 1 && (ch >= REAC_HEADAMP_MAX_CH || !value_ok(param, value) ||
		               value != reac_headamp_tx_effective(tx, ch, param)))
			abort();
		/* The emitted value is the one that the input last set for the cell, or,
		 * for a cell the input never set, the header's default. The harness keeps
		 * the value itself; the check above asks reac_headamp_tx_effective, which
		 * the scheduler's replay calls too. On box-base-1-w8 the box is refused, so
		 * no sweep runs and the scheduler alone sends the set cells.
		 * contract: include/reac/reac_headamp_tx.h:171-174, :196-201
		 * mutant: src/reac_headamp_tx.c:32 `t->value[ch][param] = value;` -> `memset(t->value, 0, sizeof t->value); t->value[ch][param] = value;`
		 * input: box-base-1-w8 */
		if (e == 1 && param < REAC_HEADAMP_NPARAMS &&
		    value != want_of(was_set, set_to, ch, param))
			abort();
		/* An emitted cell is one the input set (an edge or a re-assert), or one
		 * inside the scene armed above, clamped to the table.
		 * contract: include/reac/reac_headamp_tx.h:178-183 (the replay covers
		 * base..base+width-1, clamped; a base past the table arms nothing),
		 * :196-201 (changed cells first, then the replay)
		 * mutant: src/reac_headamp_tx.c:154 `(uint8_t)c` -> `(uint8_t)(c - 8)`
		 * input: replay-past-ceiling */
		if (e == 1 && !(ch < REAC_HEADAMP_MAX_CH && param < REAC_HEADAMP_NPARAMS &&
		                was_set[ch][param]) &&
		    !(sw != 0 && sb < REAC_HEADAMP_MAX_CH && ch >= sb && ch < sb + sw))
			abort();
		/* An unset cell goes out only in the one complete replay of the scene armed
		 * above, so at most once. An edge sends a set cell, and a re-assert sends
		 * the set cells alone (reac_headamp_tx.h:196-201).
		 * contract: include/reac/reac_headamp_tx.h:196-201
		 * mutant: src/reac_headamp_tx.c:151 `if (t->replay_set_only &&` -> `if (0 &&`
		 * input: box-base0-w8 */
		if (e == 1 && ch < REAC_HEADAMP_MAX_CH && param < REAC_HEADAMP_NPARAMS &&
		    !was_set[ch][param] && unset_sent[ch][param]++ != 0)
			abort();
	}
	free(tx);
	return 0;
}
