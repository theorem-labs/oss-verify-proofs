// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>
// Modified by Theorem Labs, 2026-10-25: a modified copy of fuzz/fuzz_disco.c at libreac 9ed322ef.

/* libFuzzer harness: DISCOVERY (src/reac_disco.c) and the HUNT built on it
 * (src/reac_hunt.c) — who is on a segment, in which role, and what the table a
 * consumer reads says about them.
 *
 * Input:  [0..5] our MAC   [6] bit 0: pin the hunt's role, bit 1: the pinned role,
 *                          bit 2: the wire was proven masterless (the knock's licence)
 *         then operations, at most 512, each [op][u16 LE dt in ms] and, for a frame
 *         operation, a u16 LE length and the frame's bytes:
 *           op & 3 == 0   classify unlocked -> announce gate -> table
 *           op & 3 == 1   classify against the segment's peer lock -> gate -> table
 *           op & 3 == 2   offer the frame to the hunt
 *           op & 3 == 3   age the table, serialise it into a buffer of
 *                         k = op >> 2 & 0x1f: (k - 1) * 41 + 2 bytes, or
 *                         REAC_DISCO_JSON_MAX for k = 0; step the hunt
 *         op & 0x04 (frame ops): bypass the gate and observe directly
 *         op & 0x08 (frame ops): the sighting is our own peer (`owned`)
 *         op & 0x10 (frame ops): the sighting carries the box family (op >> 5 & 3)
 *                    an established master learnt from the peer's identity page
 *         op & 0x80: the clock steps BACK by dt instead of forward — every age
 *                    computation here claims to survive a non-monotonic clock.
 *
 * The clock is the input's: a time the harness keeps, never a read of the real one.
 *
 * Properties, each an abort():
 *   - a sighting comes from a frame of at least 50 bytes, is the frame's own source,
 *     never our MAC; its geometry is the one the harness calculates from the frame
 *     length (for the hunt's settled verdict, at least that); outside FILLER the 32
 *     bytes of its block sum to 0 mod 256 (the harness adds them); a declared width
 *     is at most REAC_MAX_CHANNELS;
 *   - the gate, the table and the hunt's table never hold more than REAC_DISCO_MAX
 *     peers, and never the same MAC twice;
 *   - A BOX DOES NOT UN-PROVE ITSELF: an entry the table holds as a box is never
 *     turned into a master by a later sighting;
 *   - an observe changes the table as the harness calculates it: a known entry takes
 *     each fact that sharpens it and the new time, a new MAC gets an entry with the
 *     sighting's facts, a full table refuses a new MAC and marks itself overflowed;
 *     the return is 1 exactly when the table changed, and seq moves by the return,
 *     plus one on the first refusal for room;
 *   - an age removes exactly the entries that a forward clock shows unheard for more
 *     than REAC_DISCO_STALE_NS (a clock that steps back removes nothing), and seq
 *     moves once when it removes any;
 *   - a full table always serialises into REAC_DISCO_JSON_MAX, and any successful
 *     serialisation is one NUL-terminated JSON array of the length returned, with
 *     one object for each table entry, which holds the entry's MAC, role, model,
 *     width, owned flag and age in ms.
 *
 * Each property has, in its comment, one or more one-line changes to libreac
 * (`mutant:`) that make it fail, each with a seed of the corpus (`input:`) that shows
 * it.
 */
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <reac/reac.h>
#include <reac/reac_box_facts.h>
#include <reac/reac_ctrlblk.h>
#include <reac/reac_disco.h>
#include <reac/reac_hunt.h>

#include "fuzz.h"

#define MAX_OPS 512

/* The geometry of a clean frame, from the protocol and not from the library:
 * 52 bytes (50 header + 2 end marker) plus 36 bytes (12 samples x 3 B) for each
 * channel. Any other length has no geometry (0).
 * contract: include/reac/reac.h:65-66; include/reac/reac_disco.h:101-105 (the
 * sighting's width, from the frame length alone, 0 for no legal 52 + n*36) */
static unsigned frame_channels(size_t len)
{
	if (len < 52 || (len - 52) % 36 != 0)
		return 0;
	return (unsigned)((len - 52) / 36);
}

/* A capture can keep the 2 FCS bytes after the end marker. A length of 52 + n*36 + 2
 * is such a frame, and its clean length is 2 less.
 * contract: include/reac/reac.h:175-182 */
static size_t frame_clean_len(size_t len)
{
	if (len >= 54 && (len - 52) % 36 == 2)
		return len - 2;
	return len;
}

/* The role names that the JSON uses.
 * contract: include/reac/reac_disco.h:83 */
static const char *role_text(int role)
{
	switch (role) {
	case REAC_DISCO_ROLE_BOX:    return "box";
	case REAC_DISCO_ROLE_MASTER: return "master";
	default:                     return "unknown";
	}
}

static void check_table(const struct reac_disco_table *t)
{
	/* At most REAC_DISCO_MAX entries.
	 * The `t->n > REAC_DISCO_MAX` part: the entry array has REAC_DISCO_MAX slots, so
	 * no change that keeps memory safe can make it true. The sabotage patch
	 * (fuzz/sabotage/disco.patch) writes a ninth entry past the table: ASan stops it
	 * in the library, and in the plain build the write puts the ninth MAC over `n`,
	 * which this check then sees.
	 * mutant: src/reac_disco.c:366 `t->n--;` -> `t->n -= 9;`
	 * input: desk-and-box
	 * mutant: src/reac_disco.c:329 `>=` -> `>`
	 * input: nine-peers
	 */
	if (t->n < 0 || t->n > REAC_DISCO_MAX)
		abort();
	for (int i = 0; i < t->n; i++) {
		/* Each role is one of the three roles.
		 * mutant: src/reac_disco.c:343 `s->role` -> `7`
		 * input: fixture-l1-box-hb
		 * mutant: src/reac_disco.c:343 `s->role` -> `-1`
		 * input: fixture-l1-box-hb
		 */
		if ((int)t->e[i].role < REAC_DISCO_ROLE_UNKNOWN ||
		    t->e[i].role > REAC_DISCO_ROLE_MASTER)
			abort();
		for (int j = i + 1; j < t->n; j++)
			/* No MAC twice.
			 * mutant: src/reac_disco.c:255 `memcmp(t->e[i].mac, mac, 6) == 0` -> `0`
			 * input: desk-and-box
			 */
			if (memcmp(t->e[i].mac, t->e[j].mac, 6) == 0)
				abort();
	}
}

static void check_gate(const struct reac_disco_gate *g)
{
	/* At most REAC_DISCO_MAX entries. The `g->n > REAC_DISCO_MAX` part: as for the
	 * table, only a write past the gate's array can make it true; the second mutant
	 * does that, and in the plain build the ninth MAC lands on `n`.
	 * mutant: src/reac_disco.c:238 `g->n++` -> `g->n--`
	 * input: fixture-l1-box-hb
	 * mutant: src/reac_disco.c:235 `>=` -> `>`
	 * input: nine-peers
	 */
	if (g->n < 0 || g->n > REAC_DISCO_MAX)
		abort();
	for (int i = 0; i < g->n; i++)
		for (int j = i + 1; j < g->n; j++)
			/* No MAC twice.
			 * mutant: src/reac_disco.c:206 `memcmp(e->mac, s->mac, 6) != 0` -> `1`
			 * input: desk-and-box
			 */
			if (memcmp(g->e[i].mac, g->e[j].mac, 6) == 0)
				abort();
}

static int find_entry(const struct reac_disco_table *t, const uint8_t mac[6])
{
	for (int i = 0; i < t->n; i++)
		if (memcmp(t->e[i].mac, mac, 6) == 0)
			return i;
	return -1;
}

static int role_of(const struct reac_disco_table *t, const uint8_t mac[6])
{
	int i = find_entry(t, mac);
	return i < 0 ? -1 : (int)t->e[i].role;
}

/* `settled`: the hunt answers with the table's verdict for the peer, whose width is
 * the widest geometry the peer has shown, so it is at least this frame's. `len` is
 * the clean length. */
static void check_sighting(const struct reac_disco_sighting *s, const uint8_t *frame,
                           size_t len, const uint8_t our[6], int settled)
{
	/* A sighting comes from a frame of at least 50 bytes (header and control block),
	 * names the frame's source (bytes 6..11), and is never our own MAC.
	 * contract: include/reac/reac_disco.h:87 (the frame's own source), :109-110
	 * (never our own echo); include/reac/reac_ctrlblk.h:38 (the block at [18:50])
	 * mutant: src/reac_ctrlblk.c:262 `len < AUDIO_OFF` -> `len < 14`
	 * input: short-filler-49
	 * mutant: src/reac_disco.c:142 `p.src, 6` -> `p.src, 5`
	 * input: fixture-l1-box-hb
	 * mutant: src/reac_disco.c:109 `memcmp(p.src, our_mac, 6) == 0` -> `0`
	 * input: lock-and-gate
	 */
	if (len < 50 || memcmp(s->mac, frame + 6, 6) != 0 || memcmp(s->mac, our, 6) == 0)
		abort();
	/* The geometry is the frame length's (the harness calculates it). The hunt
	 * answers with the widest geometry of the peer, so it is at least this one.
	 * mutant: include/reac/reac.h:122 `REAC_UPSTREAM_BYTES_PER_CH` -> `18`
	 * input: fixture-l1-box-hb
	 * mutant: src/reac_hunt.c:88 `e->channels` -> `0`
	 * input: fixture-l1-box-hb
	 * mutant: src/reac.c:75 `len - 2` -> `len`
	 * input: box-hb-fcs-hunt
	 */
	if (settled ? s->channels < frame_channels(len)
	            : s->channels != frame_channels(len))
		abort();
	/* The role is one of the three roles.
	 * mutant: src/reac_disco.c:66 `REAC_DISCO_ROLE_BOX` -> `7`
	 * input: fixture-l1-box-hb
	 * mutant: src/reac_disco.c:66 `REAC_DISCO_ROLE_BOX` -> `-1`
	 * input: fixture-l1-box-hb
	 */
	if ((int)s->role < REAC_DISCO_ROLE_UNKNOWN || s->role > REAC_DISCO_ROLE_MASTER)
		abort();
	int filler = frame[16] == 0x00 && frame[17] == 0x00;
	unsigned sum = 0;
	for (int i = 18; i < 50; i++)
		sum += frame[i];
	/* Outside FILLER (type 00 00 at bytes 16..17), the 32 bytes of the control block
	 * (18..49) sum to 0 mod 256. The harness adds them: a corrupt frame is not
	 * evidence of a peer (reac_disco.c classify_core).
	 * contract: include/reac/reac_disco.h:109-110 (a corrupt control block is no
	 * sighting); include/reac/reac_ctrlblk.h:37-46 (the block, its sum, FILLER
	 * exempt); reac.ksy `frame_type` (0x0000: filler)
	 * mutant: src/reac_ctrlblk.c:51 `(s & 0xff) == 0 ? 0 : -1` -> `0`
	 * input: lock-and-gate
	 */
	if (!filler && (sum & 0xff) != 0)
		abort();
	/* A declared width is at most REAC_MAX_CHANNELS.
	 * contract: include/reac/reac_disco.h:89-91
	 * mutant: src/reac_disco.c:161 `(uint8_t)ports.in_ch` -> `41`
	 * input: fixture-l1-decl-82
	 * mutant: src/reac_disco.c:162 `(uint8_t)ports.out_ch` -> `41`
	 * input: fixture-l1-decl-82
	 */
	if (s->has_decl && (s->decl_in > REAC_MAX_CHANNELS || s->decl_out > REAC_MAX_CHANNELS))
		abort();
}

static void observe(struct reac_disco_table *t, const struct reac_disco_sighting *s,
                    int owned, uint64_t now)
{
	int at = find_entry(t, s->mac);
	struct reac_disco_entry old;
	memset(&old, 0, sizeof old);
	if (at >= 0)
		old = t->e[at];
	int n = t->n, overflowed = t->overflowed;
	uint32_t seq = t->seq;
	int changed = reac_disco_table_observe(t, s, owned, now);
	/* The return is 0 or 1.
	 * mutant: src/reac_disco.c:354 `return 1;` -> `return 2;`
	 * input: fixture-l1-box-hb
	 */
	if (changed != 0 && changed != 1)
		abort();
	check_table(t);
	uint32_t refused = at < 0 && n >= REAC_DISCO_MAX && !overflowed;
	/* seq moves by the return; a refusal for room moves it once more, the first
	 * time only (the table then says it is partial).
	 * contract: include/reac/reac_disco.h:207, :210-212
	 * mutant: src/reac_disco.c:325 `t->seq++;` -> `;`
	 * input: desk-and-box
	 * mutant: src/reac_disco.c:324 `if (changed)` -> `if (1)`
	 * input: desk-and-box
	 */
	if (t->seq != seq + (uint32_t)changed + refused)
		abort();
	/* A BOX DOES NOT UN-PROVE ITSELF.
	 * contract: include/reac/reac_disco.h:202-204
	 * mutant: src/reac_disco.c:291 `e->role == REAC_DISCO_ROLE_BOX` -> `0`
	 * input: box-then-bye-table
	 */
	if (at >= 0 && old.role == REAC_DISCO_ROLE_BOX &&
	    role_of(t, s->mac) == REAC_DISCO_ROLE_MASTER)
		abort();
	if (at >= 0) {
		/* What the known entry must hold now: facts only sharpen. A known role
		 * replaces the old one (except BOX to MASTER), a declaration, a slot count
		 * and a family replace the old ones, the width is the widest, owned stays
		 * once set, and the time of the last sighting is now.
		 * contract: include/reac/reac_disco.h:201-207 */
		struct reac_disco_entry want = old;
		if (s->role != REAC_DISCO_ROLE_UNKNOWN &&
		    !(old.role == REAC_DISCO_ROLE_BOX && s->role == REAC_DISCO_ROLE_MASTER))
			want.role = s->role;
		if (s->has_decl) {
			want.has_decl = 1;
			want.decl_in = s->decl_in;
			want.decl_out = s->decl_out;
		}
		if (s->announced_slots)
			want.announced_slots = s->announced_slots;
		if (s->family)
			want.family = s->family;
		if (s->channels > old.channels)
			want.channels = s->channels;
		if (owned)
			want.owned = 1;
		const struct reac_disco_entry *e = &t->e[at];
		/* The known entry holds what the harness calculates, at the same place.
		 * mutant: src/reac_disco.c:292 `e->role = s->role;` -> ``
		 * input: desk-and-box
		 * mutant: src/reac_disco.c:298 `e->decl_in = s->decl_in;` -> ``
		 * input: desk-and-box
		 * mutant: src/reac_disco.c:321 `e->owned = 1;` -> ``
		 * input: lock-and-gate
		 * mutant: src/reac_disco.c:266 `e->last_seen_ns = now_ns;` -> ``
		 * input: desk-and-box
		 */
		if (t->n != n || memcmp(e->mac, s->mac, 6) != 0 || e->role != want.role ||
		    e->has_decl != want.has_decl || e->decl_in != want.decl_in ||
		    e->decl_out != want.decl_out || e->announced_slots != want.announced_slots ||
		    e->family != want.family || e->channels != want.channels ||
		    e->owned != want.owned || e->first_seen_ns != old.first_seen_ns ||
		    e->last_seen_ns != now)
			abort();
		int differs = e->role != old.role || e->has_decl != old.has_decl ||
		              e->decl_in != old.decl_in || e->decl_out != old.decl_out ||
		              e->announced_slots != old.announced_slots ||
		              e->family != old.family || e->channels != old.channels ||
		              e->owned != old.owned;
		/* The return is 1 exactly when a fact of the entry changed (a new time
		 * alone is no change).
		 * mutant: src/reac_disco.c:293 `changed = 1;` -> ``
		 * input: desk-and-box
		 */
		if (changed != differs)
			abort();
	} else if (n < REAC_DISCO_MAX) {
		const struct reac_disco_entry *e = &t->e[n];
		/* A new MAC with room gets a new entry at the end, with the sighting's
		 * facts and now as both times, and the return is 1.
		 * contract: include/reac/reac_disco.h:209-210
		 * mutant: src/reac_disco.c:349 `e->channels = s->channels;` -> `;`
		 * input: fixture-l1-box-hb
		 * mutant: src/reac_disco.c:350 `owned ? 1 : 0` -> `0`
		 * input: nine-peers
		 */
		if (changed != 1 || t->n != n + 1 || memcmp(e->mac, s->mac, 6) != 0 ||
		    e->role != s->role || e->has_decl != s->has_decl ||
		    e->decl_in != s->decl_in || e->decl_out != s->decl_out ||
		    e->family != s->family || e->announced_slots != s->announced_slots ||
		    e->channels != s->channels || e->owned != (owned ? 1 : 0) ||
		    e->first_seen_ns != now || e->last_seen_ns != now)
			abort();
	} else {
		/* A new MAC on a full table is refused: no entry is added, the return is
		 * 0, and the table says it overflowed.
		 * contract: include/reac/reac_disco.h:210-212, :65 (REAC_DISCO_MAX)
		 * mutant: src/reac_disco.c:334 `t->overflowed = 1;` -> `;`
		 * input: nine-peers
		 */
		if (changed != 0 || t->n != n || !t->overflowed)
			abort();
	}
}

/* ---- A small JSON reader for the array that reac_disco_table_json writes. ----
 * It reads an array of objects whose values are strings, numbers, true, false or
 * null; a nested value is not accepted. It keeps the values of the keys the table
 * gives. Every loop moves forward in the buffer, so the work is at most linear in
 * the length (at most REAC_DISCO_JSON_MAX here). */
struct jtok {
	const char *p;
	size_t n;
	int kind;   /* 0: not present, 1: string (p, n: the text inside the quotes),
	             * 2: number, 3: true, false or null */
};

struct jobj {
	struct jtok mac, role, model, width, owned, age_ms;
};

static size_t json_ws(const char *b, size_t i, size_t n)
{
	while (i < n && (b[i] == ' ' || b[i] == '\t' || b[i] == '\n' || b[i] == '\r'))
		i++;
	return i;
}

static int json_digit(const char *b, size_t i, size_t n)
{
	return i < n && b[i] >= '0' && b[i] <= '9';
}

static int json_hex(char c)
{
	return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F');
}

/* Reads one string, number or literal at b[i]. Returns the index after it, or 0 when
 * it is not valid JSON (no valid value starts at index 0 here: index 0 is '['). */
static size_t json_scalar(const char *b, size_t i, size_t n, struct jtok *v)
{
	if (i >= n)
		return 0;
	if (b[i] == '"') {
		size_t j = i + 1;
		while (j < n && b[j] != '"') {
			if ((unsigned char)b[j] < 0x20)
				return 0;
			if (b[j] == '\\') {
				j++;
				if (j >= n || !strchr("\"\\/bfnrtu", b[j]) || b[j] == '\0')
					return 0;
				if (b[j] == 'u') {
					if (n - j <= 4 || !json_hex(b[j + 1]) || !json_hex(b[j + 2]) ||
					    !json_hex(b[j + 3]) || !json_hex(b[j + 4]))
						return 0;
					j += 4;
				}
			}
			j++;
		}
		if (j >= n)
			return 0;
		v->p = b + i + 1;
		v->n = j - i - 1;
		v->kind = 1;
		return j + 1;
	}
	static const char *const lit[] = { "true", "false", "null" };
	for (int k = 0; k < 3; k++) {
		size_t l = strlen(lit[k]);
		if (n - i >= l && memcmp(b + i, lit[k], l) == 0) {
			v->p = b + i;
			v->n = l;
			v->kind = 3;
			return i + l;
		}
	}
	size_t j = i;
	if (j < n && b[j] == '-')
		j++;
	if (!json_digit(b, j, n))
		return 0;
	if (b[j] == '0')
		j++;
	else
		while (json_digit(b, j, n))
			j++;
	if (j < n && b[j] == '.') {
		j++;
		if (!json_digit(b, j, n))
			return 0;
		while (json_digit(b, j, n))
			j++;
	}
	if (j < n && (b[j] == 'e' || b[j] == 'E')) {
		j++;
		if (j < n && (b[j] == '+' || b[j] == '-'))
			j++;
		if (!json_digit(b, j, n))
			return 0;
		while (json_digit(b, j, n))
			j++;
	}
	v->p = b + i;
	v->n = j - i;
	v->kind = 2;
	return j;
}

static int jtok_is(const struct jtok *v, int kind, const char *text)
{
	size_t l = strlen(text);
	return v->kind == kind && v->n == l && memcmp(v->p, text, l) == 0;
}

/* Reads b[0..n) as one JSON array of objects. Returns the count of objects, or -1
 * when the text is not such an array or an object has one of the keys twice. The
 * first `max` objects go to o[]. */
static int json_read(const char *b, size_t n, struct jobj *o, int max)
{
	size_t i = json_ws(b, 0, n);
	if (i >= n || b[i] != '[')
		return -1;
	i = json_ws(b, i + 1, n);
	int count = 0;
	if (i < n && b[i] == ']')
		return json_ws(b, i + 1, n) == n ? 0 : -1;
	for (;;) {
		struct jobj scratch;
		struct jobj *cur = count < max ? &o[count] : &scratch;
		memset(cur, 0, sizeof *cur);
		if (i >= n || b[i] != '{')
			return -1;
		i = json_ws(b, i + 1, n);
		if (i < n && b[i] == '}') {
			i++;
		} else {
			for (;;) {
				struct jtok key, val;
				size_t j = json_scalar(b, i, n, &key);
				if (!j || key.kind != 1)
					return -1;
				i = json_ws(b, j, n);
				if (i >= n || b[i] != ':')
					return -1;
				i = json_ws(b, i + 1, n);
				j = json_scalar(b, i, n, &val);
				if (!j)
					return -1;
				i = json_ws(b, j, n);
				struct jtok *slot = jtok_is(&key, 1, "mac")    ? &cur->mac
				                  : jtok_is(&key, 1, "role")   ? &cur->role
				                  : jtok_is(&key, 1, "model")  ? &cur->model
				                  : jtok_is(&key, 1, "width")  ? &cur->width
				                  : jtok_is(&key, 1, "owned")  ? &cur->owned
				                  : jtok_is(&key, 1, "age_ms") ? &cur->age_ms
				                                               : NULL;
				if (slot) {
					if (slot->kind)
						return -1;
					*slot = val;
				}
				if (i < n && b[i] == ',') {
					i = json_ws(b, i + 1, n);
					continue;
				}
				if (i < n && b[i] == '}') {
					i++;
					break;
				}
				return -1;
			}
		}
		count++;
		i = json_ws(b, i, n);
		if (i < n && b[i] == ',') {
			i = json_ws(b, i + 1, n);
			continue;
		}
		if (i < n && b[i] == ']') {
			i++;
			break;
		}
		return -1;
	}
	return json_ws(b, i, n) == n ? count : -1;
}

/* Each check below holds the serialisation to the shape the header gives: one
 * NUL-terminated array, one object per entry, and each object's mac, role, model,
 * width, owned and age_ms as it says.
 * contract: include/reac/reac_disco.h:229-230 (a full table always fits
 * REAC_DISCO_JSON_MAX), :232-244 (the return, the shape and each field) */
static void serialise(const struct reac_disco_table *t, uint64_t now, size_t cap)
{
	char *buf = malloc(cap ? cap : 1);
	/* not a property: malloc failed, so the harness has no buffer to give */
	if (!buf)
		abort();
	int r = reac_disco_table_json(t, now, buf, cap);
	/* "sized so a full table always serializes rather than being suppressed":
	 * with REAC_DISCO_JSON_MAX bytes, the serialisation is never refused.
	 * mutant: src/reac_disco.c:391 `cap < 3` -> `cap < 2000`
	 * input: fixture-l1-box-hb
	 */
	if (r == -1 && cap >= REAC_DISCO_JSON_MAX)
		abort();
	if (r != -1) {
		/* A successful serialisation: its length fits the buffer, a NUL ends it,
		 * it starts with '[' and ends with ']'.
		 * mutant: src/reac_disco.c:417 `"]"` -> `""`
		 * input: fixture-l1-box-hb
		 */
		if (r < 2 || (size_t)r >= cap || buf[r] != '\0' || strlen(buf) != (size_t)r ||
		    buf[0] != '[' || buf[r - 1] != ']')
			abort();
		struct jobj o[REAC_DISCO_MAX + 1];
		int count = json_read(buf, (size_t)r, o, REAC_DISCO_MAX + 1);
		/* It is one JSON array of objects.
		 * mutant: src/reac_disco.c:397 `i ? "," : ""` -> `""`
		 * input: desk-and-box
		 */
		if (count < 0)
			abort();
		/* One object for each table entry: never a truncated list.
		 * mutant: src/reac_disco.c:394 `i < t->n` -> `i < t->n && i < 1`
		 * input: desk-and-box
		 */
		if (count != t->n)
			abort();
		int used[REAC_DISCO_MAX] = { 0 };
		for (int i = 0; i < count && i < REAC_DISCO_MAX; i++) {
			int at = -1;
			for (int j = 0; j < t->n && at < 0; j++) {
				char mac[18];
				const uint8_t *m = t->e[j].mac;
				snprintf(mac, sizeof mac, "%02x:%02x:%02x:%02x:%02x:%02x",
				         m[0], m[1], m[2], m[3], m[4], m[5]);
				if (jtok_is(&o[i].mac, 1, mac))
					at = j;
			}
			/* Each object's "mac" names a table entry (as aa:bb:cc:dd:ee:ff), and
			 * no two objects name the same entry.
			 * mutant: src/reac_disco.c:398 `e->mac[5]` -> `e->mac[4]`
			 * input: fixture-l1-box-hb
			 */
			if (at < 0 || used[at])
				abort();
			used[at] = 1;
			const struct reac_disco_entry *e = &t->e[at];
			/* Its "role" is the entry's role.
			 * mutant: src/reac_disco.c:17 `"box"` -> `"master"`
			 * input: fixture-l1-box-hb
			 */
			if (!jtok_is(&o[i].role, 1, role_text(e->role)))
				abort();
			char nm[REAC_BOX_NAME_MAX], tok[REAC_BOX_NAME_TOKEN_MAX],
			     disp[REAC_BOX_NAME_DISPLAY_MAX], width[24];
			const char *model = "unknown";
			snprintf(width, sizeof width, "0x0");
			if (e->has_decl &&
			    reac_box_name((enum reac_box_family)e->family, NULL, e->decl_in,
			                  e->decl_out, nm, sizeof nm, tok, sizeof tok,
			                  disp, sizeof disp) == 0) {
				model = tok;
				snprintf(width, sizeof width, "%dx%d", e->decl_in, e->decl_out);
			}
			/* Its "model" is the token reac_box_name gives for the declaration, and
			 * its "width" is the declared in x out; with no usable declaration they
			 * are "unknown" and "0x0".
			 * mutant: src/reac_disco.c:408 `tok` -> `nm`
			 * input: desk-and-box
			 * mutant: src/reac_disco.c:409 `e->decl_in, e->decl_out` -> `e->decl_out, e->decl_in`
			 * input: fixture-l1-decl-82
			 */
			if (!jtok_is(&o[i].model, 1, model) || !jtok_is(&o[i].width, 1, width))
				abort();
			/* Its "owned" is the entry's owned flag, as true or false.
			 * mutant: src/reac_disco.c:414 `e->owned ? "true" : "false"` -> `"false"`
			 * input: nine-peers-full-json
			 */
			if (!jtok_is(&o[i].owned, 3, e->owned ? "true" : "false"))
				abort();
			char age[24];
			uint64_t age_ns = now > e->last_seen_ns ? now - e->last_seen_ns : 0;
			snprintf(age, sizeof age, "%llu", (unsigned long long)(age_ns / 1000000ULL));
			/* Its "age_ms" is the time since the last sighting in whole ms, 0 when
			 * the clock is before that sighting.
			 * mutant: src/reac_disco.c:415 `1000000ULL` -> `1000ULL`
			 * input: desk-and-box
			 */
			if (!jtok_is(&o[i].age_ms, 2, age))
				abort();
		}
	}
	free(buf);
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	if (size >= FUZZ_INPUT_MAX)
		return 0;
	struct fuzz_in in = fuzz_in(data, size);
	uint8_t our[6];
	for (int i = 0; i < 6; i++)
		our[i] = fuzz_u8(&in);
	uint8_t setup = fuzz_u8(&in);

	uint64_t now = 1000000000ULL;   /* one second in: the clock starts wherever it likes */
	struct reac_disco_table t;
	struct reac_disco_gate g;
	struct reac_disco_peer_lock lock;
	struct reac_hunt *h = malloc(sizeof *h);
	/* not a property: malloc failed, so the harness has no hunt to drive */
	if (!h)
		abort();
	reac_disco_table_init(&t);
	reac_disco_gate_init(&g);
	reac_disco_peer_lock_init(&lock);
	reac_hunt_init(h, our, now);
	if (setup & 1)
		reac_hunt_pin(h, (setup & 2) ? REAC_ROLE_MASTER : REAC_ROLE_SLAVE);
	if (setup & 4)
		reac_hunt_silence_proven(h);

	for (int i = 0; i < MAX_OPS && in.n; i++) {
		uint8_t op = fuzz_u8(&in);
		uint64_t dt = (uint64_t)fuzz_u16(&in) * 1000000ULL;
		if (op & 0x80)
			now = dt > now ? 0 : now - dt;
		else
			now += dt;

		if ((op & 3) == 3) {
			uint32_t seq = t.seq;
			int n = t.n, stale = 0;
			for (int j = 0; j < t.n; j++)
				if (now > t.e[j].last_seen_ns &&
				    now - t.e[j].last_seen_ns > REAC_DISCO_STALE_NS)
					stale++;
			int removed = reac_disco_table_age(&t, now);
			check_table(&t);
			int left = 0;
			for (int j = 0; j < t.n; j++)
				if (now > t.e[j].last_seen_ns &&
				    now - t.e[j].last_seen_ns > REAC_DISCO_STALE_NS)
					left++;
			/* The age removes exactly the stale entries: those that a forward
			 * clock shows unheard for more than REAC_DISCO_STALE_NS. A clock that
			 * stepped back makes no entry stale.
			 * contract: include/reac/reac_disco.h:217-219, :70
			 * mutant: src/reac_disco.c:363 `now_ns > t->e[i].last_seen_ns &&` -> ``
			 * input: box-then-clock-back
			 * mutant: src/reac_disco.c:364 `REAC_DISCO_STALE_NS` -> `0`
			 * input: desk-and-box
			 */
			if (removed != stale || t.n != n - stale || left != 0)
				abort();
			/* seq moves once when the age removes any entry, else it stays.
			 * contract: include/reac/reac_disco.h:219
			 * mutant: src/reac_disco.c:373 `t->seq++;` -> `;`
			 * input: desk-and-box
			 */
			if (t.seq != seq + (removed ? 1u : 0u))
				abort();
			size_t k = op >> 2 & 0x1f;
			serialise(&t, now, k ? (k - 1) * 41 + 2 : REAC_DISCO_JSON_MAX);
			int ch = reac_hunt_step(h, now);
			/* The hunt step returns 0 or 1.
			 * mutant: src/reac_hunt.c:268 `(v != h->verdict)` -> `2`
			 * input: fixture-l1-box-hb
			 */
			if (ch != 0 && ch != 1)
				abort();
			/* Every verdict has a name.
			 * mutant: src/reac_hunt.c:19 `"hunting"` -> `0`
			 * input: fixture-l1-box-hb
			 */
			if (!reac_hunt_verdict_name(h->verdict))
				abort();
			check_table(&h->table);
			(void)reac_hunt_role(h);
			(void)reac_hunt_heard_anything(h);
			continue;
		}

		const uint8_t *body;
		size_t len = fuzz_record(&in, &body);
		uint8_t *frame = fuzz_dup(body, len);
		struct reac_disco_sighting s;
		if ((op & 3) == 2) {
			int before = role_of(&h->table, len >= 12 ? frame + 6 : our);
			int r = reac_hunt_observe(h, frame, len, now, &s);
			/* The hunt's observe returns -1, 0 or 1.
			 * mutant: src/reac_hunt.c:65 `? 1 : 0` -> `? 2 : 0`
			 * input: fixture-l1-box-hb
			 */
			if (r < -1 || r > 1)
				abort();
			if (r >= 0) {
				check_sighting(&s, frame, frame_clean_len(len), our, 1);
				/* The hunt never answers MASTER for a MAC its table held as BOX.
				 * mutant: src/reac_disco.c:291 `e->role == REAC_DISCO_ROLE_BOX` -> `0`
				 * input: box-0832-hunt-setup0
				 * mutant: src/reac_hunt.c:82 `e->role` -> `s.role`
				 * input: box-0832-hunt-setup0
				 */
				if (before == REAC_DISCO_ROLE_BOX && s.role == REAC_DISCO_ROLE_MASTER)
					abort();
			}
			check_table(&h->table);
		} else {
			int r = (op & 3) == 0 ? reac_disco_classify(frame, len, our, &s)
			                      : reac_disco_classify_on_segment(&lock, frame, len, our, &s);
			/* Classify returns 0 or -1.
			 * mutant: src/reac_disco.c:173 `return 0;` -> `return 1;`
			 * input: fixture-l1-box-hb
			 */
			if (r != 0 && r != -1)
				abort();
			if (r == 0) {
				check_sighting(&s, frame, len, our, 0);
				int push = reac_disco_gate_should_push(&g, &s, now);
				/* The gate returns 0 or 1.
				 * mutant: src/reac_disco.c:244 `return 1;` -> `return 2;`
				 * input: fixture-l1-box-hb
				 */
				if (push != 0 && push != 1)
					abort();
				check_gate(&g);
				if (op & 0x10)
					s.family = op >> 5 & 3;
				if (push || (op & 4))
					observe(&t, &s, (op & 8) != 0, now);
			}
		}
		free(frame);
	}
	free(h);
	return 0;
}
