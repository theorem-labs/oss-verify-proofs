// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>
// Modified by Theorem Labs, 2026-10-25: a modified copy of fuzz/fuzz_boxreg.c at libreac 9ed322ef.

/* libFuzzer harness: the MULTI-BOX REGISTRY (src/reac_boxreg.c), which places each
 * box a segment carries at its own slice of the 40-slot audio fabric.
 *
 * The registry parses no bytes itself, but everything it is handed comes off the
 * wire: a JOIN's source MAC and the width a box declared. The input is a sequence
 * of the four calls a master makes, so the table is built from the input the way
 * a segment builds it.
 *
 * Input:  [0] fabric size (anything; init clamps it)
 *         then operations, at most 64, each [op] followed by its arguments:
 *           op & 3 == 0   declare: [nch][s8 base][name len % 48][name bytes]
 *           op & 3 == 1   add:     [mac][nch]
 *           op & 3 == 2   find:    [mac]
 *           op & 3 == 3   set_name:[s8 idx][name len % 48][name bytes]
 *         A [mac] is one byte, 00:40:ab:00:00:<b>, so boxes collide often; with
 *         op & 4 it is six bytes, so the all-zero "unbound" MAC is reachable too.
 *         op & 8 gives a NULL name to declare and set_name.
 *         A name is its own NUL-terminated allocation, whatever bytes it holds.
 *
 * Properties, each an abort():
 *   - no more than REAC_BOXREG_MAX_BOXES boxes, each an even 2..40 width at a base
 *     whose slice lies inside the fabric; the harness writes the width rule out
 *     itself and does not ask the library's reac_box_width_ok;
 *   - no two boxes' slices overlap and no MAC is registered twice;
 *   - declare and add give the result that reac_boxreg.h states, which the harness
 *     works out on the table before the call: a refusal for a bad width, a full
 *     table or no free range; else the lowest free range (or the pinned base),
 *     and for add first the MAC's own box, then the first unbound box of its width;
 *   - a pinned declaration lands at the base it asked for, with `pinned` set, and
 *     only a pinned one has `pinned` set; a declared name is stored;
 *   - no call moves a box, changes its width or `pinned`, unbinds or rebinds its
 *     MAC, or changes a name other than the one set_name sets;
 *   - add is idempotent and find finds what add registered; the zero MAC is never
 *     a box;
 *   - every name is NUL-terminated inside its field.
 *
 * Each property's comment records a mutant (a one-line change that makes the
 * library wrong on purpose) and a seed of fuzz_boxreg_seed_corpus.zip on which
 * the property stops it.
 */
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include <reac/reac_boxreg.h>

#include "fuzz.h"

#define MAX_OPS 64

static const uint8_t ZERO[6];

static void read_mac(struct fuzz_in *in, int full, uint8_t mac[6])
{
	if (full) {
		for (int i = 0; i < 6; i++)
			mac[i] = fuzz_u8(in);
	} else {
		static const uint8_t base[5] = { 0x00, 0x40, 0xab, 0x00, 0x00 };
		memcpy(mac, base, 5);
		mac[5] = fuzz_u8(in);
	}
}

static char *read_name(struct fuzz_in *in)
{
	const uint8_t *p;
	size_t n = fuzz_take(in, fuzz_u8(in) % 48, &p);
	char *s = malloc(n + 1);
	/* not a property: the allocation of the name copy failed */
	if (!s)
		abort();
	memcpy(s, p, n);
	s[n] = '\0';
	return s;
}

/* The width rule, written out here and not taken from the library: a box is an
 * even 2..40 channels wide (reac_boxreg.h, reac.h), and no wider than the fabric.
 * contract: include/reac/reac_facts_box_width.h:43, :51 (2 and 40),
 * include/reac/reac.h:70-71 (even per direction), include/reac/reac_boxreg.h:56
 * (`nch` slots, even) */
static int legal_width(int nch, int fabric)
{
	return nch >= 2 && nch <= 40 && nch % 2 == 0 && nch <= fabric;
}

/* Is [base, base + nch) inside the fabric and clear of each box of t? */
static int range_free(const struct reac_boxreg *t, int base, int nch, int fabric)
{
	if (base < 0 || base > fabric - nch)
		return 0;
	for (int i = 0; i < t->n; i++)
		if (base < t->box[i].base + t->box[i].nch && t->box[i].base < base + nch)
			return 0;
	return 1;
}

/* The lowest free range of nch slots in t, or -1 (reac_boxreg.h: "the lowest free
 * contiguous range").
 * contract: include/reac/reac_boxreg.h:57-58, :64 */
static int lowest_free(const struct reac_boxreg *t, int nch, int fabric)
{
	for (int base = 0; base <= fabric - nch; base++)
		if (range_free(t, base, nch, fabric))
			return base;
	return -1;
}

static void check(const struct reac_boxreg *r, int fabric)
{
	/* mutant: src/reac_boxreg.c:12 `r->fabric =` -> `r->n = -1; r->fabric =`
	 * input: fabric-full
	 * mutant: src/reac_boxreg.c:12 `r->fabric =` -> `r->n = 6; r->fabric =`
	 * input: fabric-full
	 * mutant: src/reac_boxreg.c:12 `? fabric :` -> `? fabric - 1 :`
	 * input: fabric-full
	 */
	if (r->n < 0 || r->n > REAC_BOXREG_MAX_BOXES || r->fabric != fabric)
		abort();
	for (int i = 0; i < r->n; i++) {
		const struct reac_box *b = &r->box[i];
		/* The width rule of legal_width, a base of 0 or more, and the slice ends
		 * inside the fabric.
		 * mutant: src/reac_boxreg.c:126 `snprintf(` -> `r->box[idx].nch |= 1, snprintf(`
		 * input: collisions
		 * mutant: src/reac_boxreg.c:126 `snprintf(` -> `r->box[idx].base = -1, snprintf(`
		 * input: collisions
		 * mutant: src/reac_boxreg.c:126 `snprintf(` -> `r->box[idx].base = 20, snprintf(`
		 * input: collisions
		 */
		if (!legal_width(b->nch, r->fabric) || b->base < 0 || b->base + b->nch > r->fabric)
			abort();
		/* mutant: src/reac_boxreg.c:126 `sizeof r->box[idx].name` -> `sizeof r->box[idx].name + 1`
		 * input: collisions
		 */
		if (memchr(b->name, 0, sizeof b->name) == NULL)
			abort();
		for (int j = i + 1; j < r->n; j++) {
			const struct reac_box *c = &r->box[j];
			/* Two boxes on one slot.
			 * mutant: src/reac_boxreg.c:126 `snprintf(` -> `r->box[idx].base = 0, snprintf(`
			 * input: collisions
			 */
			if (b->base < c->base + c->nch && c->base < b->base + b->nch)
				abort();
			/* mutant: src/reac_boxreg.c:126 `snprintf(` -> `memcpy(r->box[idx].mac, r->box[0].mac, 6), snprintf(`
			 * input: declare-then-join
			 */
			if (memcmp(b->mac, ZERO, 6) != 0 && memcmp(b->mac, c->mac, 6) == 0)
				abort();
		}
	}
}

/* Each box of prev (the table before the call) keeps its base, width and
 * `pinned`, a bound MAC stays bound to it, and its name stays unless set_name set
 * it (renamed is that index, or -1). The library has no call that moves, resizes
 * or removes a box, and add binds only an unbound one. */
static void check_kept(const struct reac_boxreg *r, const struct reac_boxreg *prev, int renamed)
{
	for (int i = 0; i < prev->n; i++) {
		const struct reac_box *a = &prev->box[i], *b = &r->box[i];
		/* mutant: src/reac_boxreg.c:103 `memcpy(r->box[i].mac, mac, 6);` -> `memcpy(r->box[i].mac, mac, 6); r->box[i].base = 0;`
		 * input: pinned-then-join
		 * mutant: src/reac_boxreg.c:126 `snprintf(` -> `r->box[idx].nch = 2, snprintf(`
		 * input: collisions
		 * mutant: src/reac_boxreg.c:103 `memcpy(r->box[i].mac, mac, 6);` -> `memcpy(r->box[i].mac, mac, 6); r->box[i].pinned = 0;`
		 * input: pinned-then-join
		 * mutant: src/reac_boxreg.c:126 `snprintf(` -> `memset(r->box[idx].mac, 0, 6), snprintf(`
		 * input: declare-then-join
		 * mutant: src/reac_boxreg.c:103 `memcpy(r->box[i].mac, mac, 6);` -> `memcpy(r->box[i].mac, mac, 6); r->box[i].name[0] = 0;`
		 * input: declare-then-join
		 */
		if (b->base != a->base || b->nch != a->nch || b->pinned != a->pinned ||
		    (memcmp(a->mac, ZERO, 6) != 0 && memcmp(a->mac, b->mac, 6) != 0) ||
		    (i != renamed && strncmp(a->name, b->name, sizeof a->name) != 0))
			abort();
	}
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	if (size >= FUZZ_INPUT_MAX)
		return 0;
	struct fuzz_in in = fuzz_in(data, size);
	/* Its own allocation, so a box written past the table is a sanitizer report. */
	struct reac_boxreg *r = malloc(sizeof *r);
	/* not a property: the allocation of the registry failed */
	if (!r)
		abort();
	int fabric_in = (int8_t)fuzz_u8(&in);
	reac_boxreg_init(r, fabric_in);
	/* contract: include/reac/reac_boxreg.h:50 (0 or more than the fabric -> 40) */
	int fabric =(fabric_in > 0 && fabric_in <= REAC_BOXREG_FABRIC) ? fabric_in
	                                                                : REAC_BOXREG_FABRIC;
	check(r, fabric);

	for (int i = 0; i < MAX_OPS && in.n; i++) {
		uint8_t op = fuzz_u8(&in);
		uint8_t mac[6];
		int n_before = r->n;
		int renamed = -1;
		/* The table before the call; check() has passed on it, so n_before <= 5. */
		struct reac_boxreg prev;
		memcpy(&prev, r, sizeof prev);
		switch (op & 3) {
		case 0: {
			int nch = fuzz_u8(&in);
			int base = (int8_t)fuzz_u8(&in);
			char *name = read_name(&in);
			const char *given = (op & 8) ? NULL : name;
			/* The result reac_boxreg.h gives: a refusal (-1) for a bad width or a
			 * full table; else the pinned base if that range is free, or the
			 * lowest free range for base < 0; else a refusal.
			 * contract: include/reac/reac_boxreg.h:56-59, :23 (REAC_BOXREG_MAX_BOXES) */
			int want = -1;
			if (legal_width(nch, fabric) && n_before < REAC_BOXREG_MAX_BOXES)
				want = base >= 0 ? (range_free(&prev, base, nch, fabric) ? base : -1)
				                 : lowest_free(&prev, nch, fabric);
			int idx = reac_boxreg_declare(r, nch, given, base);
			/* A new box takes the next row.
			 * mutant: src/reac_boxreg.c:83 `return r->n++;` -> `return r->n++ + 1;`
			 * input: no-room
			 * The sabotage patch fuzz/sabotage/boxreg.patch. On no-room op 5 the
			 * sixth box is written past the table. ASan reports that write first.
			 * In the plain build the write zeroes `n`, declare returns 0, and this
			 * check stops it.
			 * mutant: src/reac_boxreg.c:62 ` || r->n >= REAC_BOXREG_MAX_BOXES` -> ``
			 * input: no-room
			 */
			if (idx != -1 && idx != n_before)
				abort();
			/* mutant: src/reac_boxreg.c:83 `return r->n++;` -> `return r->n;`
			 * input: no-room
			 * mutant: src/reac_boxreg.c:79 `b->nch = nch;` -> `b->nch = nch + 2;`
			 * input: no-room
			 * mutant: src/reac_boxreg.c:77 `memset(b, 0, sizeof *b);` -> `memset(b, 0, sizeof *b); b->mac[5] = 1;`
			 * input: no-room
			 */
			if (idx >= 0 && (r->n != n_before + 1 || r->box[idx].nch != nch ||
			                 memcmp(r->box[idx].mac, ZERO, 6) != 0))
				abort();
			/* `pinned` is set exactly when a base was given, and the box is at it.
			 * mutant: src/reac_boxreg.c:80 `b->pinned = pinned;` -> `b->pinned = 1;`
			 * input: no-room
			 * mutant: src/reac_boxreg.c:80 `b->pinned = pinned;` -> `b->pinned = 0;`
			 * input: collisions
			 * mutant: src/reac_boxreg.c:78 `b->base = base;` -> `b->base = base + 2;`
			 * input: collisions
			 */
			if (idx >= 0 && (r->box[idx].pinned != (base >= 0) ||
			                 (base >= 0 && r->box[idx].base != base)))
				abort();
			/* The declared name is stored, cut to 31 characters; a NULL name is "".
			 * contract: include/reac/reac_boxreg.h:24, :41 (a 32-byte field), :57
			 * (NULL or "" is none)
			 * mutant: src/reac_boxreg.c:81 `if (name)` -> `if (0)`
			 * input: declare-then-join
			 */
			if (idx >= 0 && strncmp(r->box[idx].name, given ? given : "",
			                        REAC_BOXREG_NAME_MAX - 1) != 0)
				abort();
			/* A refused declare adds no row.
			 * mutant: src/reac_boxreg.c:70 `return -1;` -> `return r->n++, -1;`
			 * input: collisions
			 */
			if (idx < 0 && r->n != n_before)
				abort();
			/* mutant: include/reac/reac.h:86 ` && (n & 1) == 0` -> ``
			 * input: declare-odd-width
			 * mutant: src/reac_boxreg.c:48 `int base = 0` -> `int base = 1`
			 * input: no-room
			 * mutant: src/reac_boxreg.c:69 `base > r->fabric - nch` -> `base >= r->fabric - nch`
			 * input: pinned-at-end
			 */
			if (idx != (want >= 0 ? n_before : -1) || (idx >= 0 && r->box[idx].base != want))
				abort();
			free(name);
			break;
		}
		case 1: {
			read_mac(&in, op & 4, mac);
			int nch = fuzz_u8(&in);
			int nonzero = memcmp(mac, ZERO, 6) != 0;
			/* The result reac_boxreg.h gives, from the table before the call: a
			 * refusal for a bad width or the zero MAC; else the box that holds
			 * this MAC; else the first unbound box of this width; else a new row
			 * at the lowest free range; else (full table, no range) a refusal.
			 * contract: include/reac/reac_boxreg.h:62-67 */
			int held = -1, bind = -1, lf = -1, want = -1;
			for (int j = 0; j < prev.n; j++) {
				if (held < 0 && nonzero && memcmp(prev.box[j].mac, mac, 6) == 0)
					held = j;
				if (bind < 0 && memcmp(prev.box[j].mac, ZERO, 6) == 0 && prev.box[j].nch == nch)
					bind = j;
			}
			if (legal_width(nch, fabric) && nonzero) {
				if (held >= 0)
					want = held;
				else if (bind >= 0)
					want = bind;
				else if (n_before < REAC_BOXREG_MAX_BOXES &&
				         (lf = lowest_free(&prev, nch, fabric)) >= 0)
					want = n_before;
			}
			int known = reac_boxreg_find(r, mac);
			int idx = reac_boxreg_add(r, mac, nch);
			/* The zero MAC marks an unbound slot, never a box.
			 * mutant: src/reac_boxreg.c:93 `if (mac_is_zero(mac))` -> `if (0)`
			 * input: add-zero-mac
			 */
			if (!nonzero && idx != -1)
				abort();
			/* Idempotent: a known MAC gives its own box, whatever width it asks.
			 * mutant: src/reac_boxreg.c:96 `if (idx >= 0)` -> `if (idx >= 0 && r->box[idx].nch == nch)`
			 * input: rejoin-other-width
			 */
			if (known >= 0 && legal_width(nch, fabric) && idx != known)
				abort();
			/* mutant: src/reac_boxreg.c:119 `return r->n++;` -> `return r->n++ + 1;`
			 * input: fabric-full
			 * mutant: src/reac_boxreg.c:116 `memcpy(b->mac, mac, 6);` -> `memcpy(b->mac, mac, 5);`
			 * input: fabric-full
			 * mutant: src/reac_boxreg.c:29 `return i;` -> `return i + 1;`
			 * input: fabric-full
			 * mutant: src/reac_boxreg.c:97 `return idx;` -> `return idx + 1;`
			 * input: fabric-full
			 */
			if (idx >= 0 && (idx >= r->n || memcmp(r->box[idx].mac, mac, 6) != 0 ||
			                 reac_boxreg_find(r, mac) != idx ||
			                 reac_boxreg_add(r, mac, nch) != idx))
				abort();
			/* A new registration has the asked width.
			 * mutant: src/reac_boxreg.c:118 `b->nch = nch;` -> `b->nch = nch + 2;`
			 * input: fabric-full
			 */
			if (idx >= 0 && known < 0 && r->box[idx].nch != nch)
				abort();
			/* A new row is at the lowest free range and is not pinned.
			 * mutant: include/reac/reac.h:86 ` && (n & 1) == 0` -> ``
			 * input: add-odd-width
			 * mutant: include/reac/reac_facts_box_width.h:43 `2` -> `0`
			 * input: add-zero-width
			 * mutant: src/reac_boxreg.c:101 `i < r->n` -> `i < 0`
			 * input: declare-then-join
			 * mutant: src/reac_boxreg.c:48 `int base = 0` -> `int base = 1`
			 * input: fabric-full
			 * mutant: src/reac_boxreg.c:112 `if (base < 0)` -> `if (base <= 0)`
			 * input: fabric-full
			 * mutant: src/reac_boxreg.c:118 `b->nch = nch;` -> `b->nch = nch; b->pinned = 1;`
			 * input: fabric-full
			 */
			if (idx != want || (want == n_before && (r->box[idx].base != lf || r->box[idx].pinned != 0)))
				abort();
			break;
		}
		case 2: {
			read_mac(&in, op & 4, mac);
			int idx = reac_boxreg_find(r, mac);
			/* mutant: src/reac_boxreg.c:30 `return -1;` -> `return -2;`
			 * input: find-absent
			 * mutant: src/reac_boxreg.c:30 `return -1;` -> `return r->n;`
			 * input: find-absent
			 */
			if (idx < -1 || idx >= r->n)
				abort();
			/* mutant: src/reac_boxreg.c:28 `memcmp(r->box[i].mac, mac, 6)` -> `memcmp(r->box[i].mac, mac, 5)`
			 * input: find-near-mac
			 */
			if (idx >= 0 && memcmp(r->box[idx].mac, mac, 6) != 0)
				abort();
			/* mutant: src/reac_boxreg.c:25 `if (mac_is_zero(mac))` -> `if (0)`
			 * input: find-zero-mac
			 */
			if (memcmp(mac, ZERO, 6) == 0 && idx != -1)
				abort();
			break;
		}
		default: {
			int idx = (int8_t)fuzz_u8(&in);
			char *name = read_name(&in);
			reac_boxreg_set_name(r, idx, (op & 8) ? NULL : name);
			if (idx >= 0 && idx < n_before)
				renamed = idx;
			/* mutant: src/reac_boxreg.c:126 `name ? name : ""` -> `""`
			 * input: declare-then-join
			 */
			if (renamed >= 0 && strncmp(r->box[idx].name, (op & 8) ? "" : name,
			                            REAC_BOXREG_NAME_MAX - 1) != 0)
				abort();
			free(name);
			break;
		}
		}
		check(r, fabric);
		check_kept(r, &prev, renamed);
	}
	free(r);
	return 0;
}
