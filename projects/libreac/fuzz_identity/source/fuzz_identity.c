// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>
// Modified by Theorem Labs, 2026-10-25: a modified copy of fuzz/fuzz_identity.c at libreac 9ed322ef.

/* libFuzzer harness: the IDENTITY PAGE decode (src/reac_identity.c) and the box
 * naming it feeds (src/reac_box_facts.c).
 *
 * Input:  records, at most 64, each [u16 LE addr_lo][u8 len][len payload bytes]:
 *         the DT1 replies off tag 0x0500 a box sends one address at a time. The
 *         harness biases addr_lo onto the three addresses the decode models when
 *         the record's top bit pattern asks for it (see pick_addr), so the
 *         fuzzer does not have to guess 16-bit constants.
 *         Then a tail: [family][in_ch][out_ch][cap_fw][cap_ver][cap_name]
 *         [cap_token][cap_display][catalogue row][u16 LE any firmware value].
 *
 * Every payload and every output buffer is its own allocation of exactly the
 * length or capacity the input chose (of 1 byte when an output capacity is 0;
 * a payload of length 0 is malloc(0)), so a read or write past it is a
 * sanitizer report rather than a quiet stray byte. Each record is then decoded
 * a second time from a copy with one non-NUL guard byte after the payload, so
 * that the build with no sanitizer also sees a read past the payload.
 *
 * Properties, each an abort():
 *   - a well-formed record is accepted: firmware with four bytes 0..9, a REAC
 *     version of eight bytes or more, a model name with a non-NUL first byte;
 *     an ignored record changes nothing; an unmodelled address is ignored;
 *     the decode reads no byte past the length it is given;
 *   - an accepted firmware reply is four decimal digits, and reac_identity_fw_str
 *     prints exactly those digits as D.DDD;
 *   - an accepted model name is the payload's bytes up to its first NUL, never
 *     empty, NUL-terminated inside the struct;
 *   - an accepted REAC-version record keeps the raw eight bytes and decodes the
 *     last three words big-endian, and reac_identity_reac_ver_str prints them
 *     as major "." minor and the patch with two digits or more ((2,3,2) is
 *     "2.302");
 *   - reac_identity_fw_str prints any value as its whole part, ".", and three
 *     digits, also when the whole part has two digits;
 *   - every formatter either refuses or writes a NUL-terminated string inside the
 *     capacity it was given, of the length it returns;
 *   - reac_box_name refuses a bad width, and with good widths it succeeds exactly
 *     when each buffer holds its string: the name is the stem (the name the box
 *     sent, else the family's stem) with "-" and the two two-digit widths unless
 *     the stem ends in them, the token is the name lower-cased with its first '-'
 *     dropped, and the display is "<name> (<in> in / <out> out)";
 *   - reac_box_catalogue_defect sets WIDTH exactly when the entry's widths differ,
 *     and NAME exactly when the entry has a display and that display differs.
 *
 * Each property has, in its comment, one or more mutant records: a one-line
 * change to the library that makes it wrong, and the seed on which the property
 * stops that change.
 */
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include <reac/reac.h>
#include <reac/reac_box_facts.h>
#include <reac/reac_ctrlblk.h>
#include <reac/reac_identity.h>

#include "fuzz.h"

#define MAX_RECORDS 64

static uint16_t pick_addr(uint16_t raw)
{
	switch (raw >> 14) {
	case 0:  return REAC_IDENTITY_ADDR_FIRMWARE;
	case 1:  return REAC_IDENTITY_ADDR_REAC_VERSION;
	case 2:  return REAC_IDENTITY_ADDR_MODEL_NAME;
	default: return raw;   /* 0xC000-0xFFFF: an address the decode does not model */
	}
}

static char *buf_of(size_t cap)
{
	char *b = malloc(cap ? cap : 1);
	/* not a property: malloc failed */
	if (!b)
		abort();
	return b;
}

/* Append the decimal of v, with at least min digits, at b[*n]. The caller's
 * buffer holds it: v has at most ten digits and min is at most 3. */
static void put_dec(char *b, size_t *n, unsigned v, unsigned min)
{
	char d[10];
	unsigned k = 0;
	do {
		d[k++] = (char)('0' + v % 10u);
		v /= 10u;
	} while (v);
	while (k < min)
		d[k++] = '0';
	while (k)
		b[(*n)++] = d[--k];
}

static void put_str(char *b, size_t *n, const char *s)
{
	while (*s)
		b[(*n)++] = *s++;
}

/* reac_box_facts.h: a width is 0, or an even box width (2..40). */
static int width_ok(int v)
{
	return v == 0 || (v >= 2 && v <= 40 && v % 2 == 0);
}

/* reac_box_facts.h:43: the stem of each family. */
static const char *stem_of(int f)
{
	switch (f) {
	case REAC_BOX_FAMILY_S0808:  return "S-0808";
	case REAC_BOX_FAMILY_S1608:  return "S-1608";
	case REAC_BOX_FAMILY_S4000S: return "S-4000S";
	default:                     return "REAC";
	}
}

/* The family each hw block names: the 0x0600 record's eight bytes, four u16be
 * (reserved, major, minor, patch). Any other hw block names no family.
 * contract: include/reac/reac_box_facts.h:29-35 (the table), :37-40 (the one
 * recognition rule: any other value, or no 0x0600 reply, is UNKNOWN) */
static const struct {
	enum reac_box_family f;
	uint8_t hw[REAC_IDENTITY_REAC_VER_LEN];
} HW_TABLE[] = {
	{ REAC_BOX_FAMILY_S0808,  { 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00 } },
	{ REAC_BOX_FAMILY_S1608,  { 0x00, 0x00, 0x00, 0x02, 0x00, 0x03, 0x00, 0x02 } },
	{ REAC_BOX_FAMILY_S4000S, { 0x00, 0x00, 0x00, 0x02, 0x00, 0x01, 0x00, 0x02 } },
};

/* The last 0x0600 payload that ingest accepted, its first eight bytes. */
struct last_hw {
	int have;
	uint8_t hw[REAC_IDENTITY_REAC_VER_LEN];
};

static enum reac_box_family family_of_hw(const struct last_hw *h)
{
	if (!h->have)
		return REAC_BOX_FAMILY_UNKNOWN;
	for (size_t i = 0; i < sizeof HW_TABLE / sizeof HW_TABLE[0]; i++)
		if (memcmp(h->hw, HW_TABLE[i].hw, sizeof h->hw) == 0)
			return HW_TABLE[i].f;
	return REAC_BOX_FAMILY_UNKNOWN;
}

/* Two identities are equal field by field. */
static int same_id(const struct reac_identity *a, const struct reac_identity *b)
{
	return a->fw_milli == b->fw_milli && a->has_fw == b->has_fw &&
	       memcmp(a->model_name, b->model_name, sizeof a->model_name) == 0 &&
	       a->has_model_name == b->has_model_name &&
	       a->reac_version_major == b->reac_version_major &&
	       a->reac_version_minor == b->reac_version_minor &&
	       a->reac_version_patch == b->reac_version_patch &&
	       memcmp(a->reac_version_raw, b->reac_version_raw, sizeof a->reac_version_raw) == 0 &&
	       a->has_reac_version == b->has_reac_version;
}

/* A formatter's output: refused (<0), or a string of length r inside cap. */
static void check_str(int r, const char *out, size_t cap)
{
	if (r < 0)
		return;
	/* mutant: src/reac_identity.c:113 `return w;` -> `return w - 1;`
	 * input: catalogue-s1608 */
	if ((size_t)r >= cap || out[r] != '\0' || strlen(out) != (size_t)r)
		abort();
}

static void ingest(struct reac_identity *id, struct last_hw *hw, uint16_t addr,
                   const uint8_t *pl, size_t n)
{
	struct reac_identity before = *id;
	int r = reac_identity_ingest(id, addr, pl, n);
	/* Neither argument is NULL, so the decode does not refuse with -1.
	 * mutant: src/reac_identity.c:92 `return 0;` -> `return -1;`
	 * input: refusals-and-small-buffers */
	if (r < 0)
		abort();
	/* The same record again, from a copy with one non-NUL guard byte after it.
	 * This call comes after the exact-size call, so that ASan still sees a read
	 * past the exact-size copy first. */
	uint8_t *g = (uint8_t *)buf_of(n + 1);
	if (n)
		memcpy(g, pl, n);
	g[n] = 'Z';
	struct reac_identity again = before;
	int r2 = reac_identity_ingest(&again, addr, g, n);
	free(g);
	/* The decode reads no byte past the length it is given: with the guard
	 * byte it gives the same result and the same identity.
	 * The change of fuzz/sabotage/identity.patch: the decode reads one byte past
	 * a name with no NUL. ASan stops it in its builds at the first call. In the
	 * other two builds this check stops it, because the guard byte goes into
	 * the name.
	 * mutant: src/reac_identity.c:42 `n = len - 1` -> `n = len`
	 * input: name-no-nul-sabotage
	 * A firmware decode that reads a fourth byte of a three-byte reply: the
	 * guard byte is not a digit, so the result changes.
	 * mutant: src/reac_identity.c:25 `len < 4` -> `len < 3`
	 * input: refusals-and-small-buffers
	 * A version decode that accepts a seven-byte reply reads an eighth byte.
	 * mutant: src/reac_identity.c:83 `len < REAC_IDENTITY_REAC_VER_LEN` -> `len < 7`
	 * input: refusals-and-small-buffers */
	if (r2 != r || !same_id(&again, id))
		abort();
	if (r == 0) {
		/* An ignored record changes nothing.
		 * mutant: src/reac_identity.c:75 `return 0;` -> `{ id->has_fw = 1; return 0; }`
		 * input: refusals-and-small-buffers */
		if (memcmp(&before, id, sizeof before) != 0)
			abort();
		/* A firmware record of four bytes 0..9 or more is accepted.
		 * mutant: src/reac_identity.c:71 `switch (addr_lo)` -> `switch (addr_lo | 0x8000)`
		 * input: catalogue-s1608 */
		if (addr == REAC_IDENTITY_ADDR_FIRMWARE && n >= 4 &&
		    pl[0] <= 9 && pl[1] <= 9 && pl[2] <= 9 && pl[3] <= 9)
			abort();
		/* A REAC-version record of eight bytes or more is accepted.
		 * mutant: src/reac_identity.c:83 `len < REAC_IDENTITY_REAC_VER_LEN` -> `len <= REAC_IDENTITY_REAC_VER_LEN`
		 * input: catalogue-s1608 */
		if (addr == REAC_IDENTITY_ADDR_REAC_VERSION && n >= REAC_IDENTITY_REAC_VER_LEN)
			abort();
		/* A model-name record with a kind byte and a non-NUL first name byte is
		 * accepted.
		 * mutant: src/reac_identity.c:40 `len < 2` -> `len < 20`
		 * input: fixture-s0808-name */
		if (addr == REAC_IDENTITY_ADDR_MODEL_NAME && n >= 2 && pl[1] != 0)
			abort();
		return;
	}
	switch (addr) {
	case REAC_IDENTITY_ADDR_FIRMWARE: {
		/* mutant: src/reac_identity.c:77 `id->has_fw = 1;` -> ``
		 * input: catalogue-s1608 */
		if (n < 4 || !id->has_fw)
			abort();
		for (int i = 0; i < 4; i++)
			/* mutant: src/reac_identity.c:28 `p[i] > 9` -> `p[i] > 10`
			 * input: refusals-and-small-buffers */
			if (pl[i] > 9)
				abort();
		/* mutant: src/reac_identity.c:30 `p[1] * 100` -> `p[1] * 10`
		 * input: catalogue-s1608 */
		if (id->fw_milli != pl[0] * 1000 + pl[1] * 100 + pl[2] * 10 + pl[3])
			abort();
		char s[REAC_IDENTITY_FW_STR_CAP];
		int w = reac_identity_fw_str(id->fw_milli, s, sizeof s);
		check_str(w, s, sizeof s);
		/* mutant: src/reac_identity.c:109 `(frac / 100) % 10` -> `(frac / 10) % 10`
		 * input: catalogue-s1608 */
		if (w != 5 || s[0] != '0' + pl[0] || s[1] != '.' || s[2] != '0' + pl[1] ||
		    s[3] != '0' + pl[2] || s[4] != '0' + pl[3])
			abort();
		break;
	}
	case REAC_IDENTITY_ADDR_MODEL_NAME: {
		const char *nul = memchr(id->model_name, 0, sizeof id->model_name);
		/* mutant: src/reac_identity.c:54 `id->has_model_name = 1;` -> ``
		 * input: fixture-s0808-name */
		if (!id->has_model_name || !nul)
			abort();
		size_t w = (size_t)(nul - id->model_name);
		/* mutant: src/reac_identity.c:51 `w == 0` -> `w == 99`
		 * input: refusals-and-small-buffers */
		if (w == 0)
			abort();
		/* mutant: src/reac_identity.c:49 `(char)p[1 + i]` -> `(char)(p[1 + i] + 1)`
		 * input: fixture-s0808-name */
		if (n < 1 + w || memcmp(id->model_name, pl + 1, w) != 0)
			abort();
		/* mutant: src/reac_identity.c:47 `p[1 + i] == 0x00` -> `p[1 + i] == 0x38`
		 * input: fixture-s0808-name */
		if (n > 1 + w && w < REAC_IDENTITY_NAME_CAP - 1 && pl[1 + w] != 0)
			abort();   /* stopped early without a NUL to stop at */
		break;
	}
	case REAC_IDENTITY_ADDR_REAC_VERSION: {
		/* A decode that accepts fewer than eight bytes reads past the payload,
		 * so the guard-byte check above stops it first (its record at :83).
		 * mutant: src/reac_identity.c:89 `id->has_reac_version = 1;` -> ``
		 * input: catalogue-s1608
		 * mutant: src/reac_identity.c:85 `payload, REAC_IDENTITY_REAC_VER_LEN` -> `payload, REAC_IDENTITY_REAC_VER_LEN - 1`
		 * input: catalogue-s1608
		 * mutant: src/reac_identity.c:86 `payload + 2` -> `payload + 4`
		 * input: catalogue-s1608
		 * mutant: src/reac_identity.c:87 `payload + 4` -> `payload + 6`
		 * input: catalogue-s1608
		 * mutant: src/reac_identity.c:88 `payload + 6` -> `payload + 4`
		 * input: catalogue-s1608 */
		if (n < REAC_IDENTITY_REAC_VER_LEN || !id->has_reac_version ||
		    memcmp(id->reac_version_raw, pl, REAC_IDENTITY_REAC_VER_LEN) != 0 ||
		    id->reac_version_major != (uint16_t)(pl[2] << 8 | pl[3]) ||
		    id->reac_version_minor != (uint16_t)(pl[4] << 8 | pl[5]) ||
		    id->reac_version_patch != (uint16_t)(pl[6] << 8 | pl[7]))
			abort();
		/* The version string at the documented capacity: major "." minor, then
		 * the patch with two digits or more (reac_identity.h:130-134). */
		char v[REAC_IDENTITY_REAC_VER_STR_CAP], ev[24];
		size_t en = 0;
		put_dec(ev, &en, id->reac_version_major, 1);
		ev[en++] = '.';
		put_dec(ev, &en, id->reac_version_minor, 1);
		put_dec(ev, &en, id->reac_version_patch, 2);
		ev[en] = '\0';
		int w = reac_identity_reac_ver_str(id->reac_version_major, id->reac_version_minor,
		                                   id->reac_version_patch, v, sizeof v);
		/* mutant: src/reac_identity.c:134 `cap < REAC_IDENTITY_REAC_VER_STR_CAP` -> `cap <= REAC_IDENTITY_REAC_VER_STR_CAP`
		 * input: header-example-1
		 * mutant: src/reac_identity.c:141 `major` -> `minor`
		 * input: header-example-1
		 * mutant: src/reac_identity.c:144 `patch < 10` -> `patch < 1`
		 * input: header-example-1 */
		if (w < 0 || (size_t)w != en || memcmp(v, ev, en + 1) != 0)
			abort();
		hw->have = 1;
		memcpy(hw->hw, pl, sizeof hw->hw);
		break;
	}
	default:
		/* The decode accepted an address it does not model.
		 * mutant: src/reac_identity.c:92 `return 0;` -> `return 1;`
		 * input: refusals-and-small-buffers */
		abort();
	}
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	if (size >= FUZZ_INPUT_MAX)
		return 0;
	struct fuzz_in in = fuzz_in(data, size);
	struct reac_identity id;
	reac_identity_init(NULL);   /* a NULL identity is ignored, not dereferenced */
	reac_identity_init(&id);
	/* mutant: src/reac_identity.c:68 `!id ||` -> ``
	 * input: catalogue-s1608
	 * mutant: src/reac_box_facts.c:133 `return 0;` -> `return 4;`
	 * input: catalogue-s1608
	 * mutant: src/reac_box_facts.c:24 `REAC_BOX_FAMILY_UNKNOWN` -> `REAC_BOX_FAMILY_S1608`
	 * input: catalogue-s1608 */
	if (reac_identity_ingest(NULL, 0, NULL, 0) != -1 ||
	    reac_identity_ingest(&id, 0, NULL, 4) != -1 ||
	    reac_identity_fw_str(0, NULL, 8) >= 0 ||
	    reac_identity_reac_ver_str(0, 0, 0, NULL, 20) >= 0 ||
	    reac_box_catalogue_defect(NULL, 8, 8, "x") != 0 ||
	    reac_box_family_of(NULL) != REAC_BOX_FAMILY_UNKNOWN)
		abort();

	struct last_hw hw = { 0, { 0 } };
	int nrec = fuzz_u8(&in) % (MAX_RECORDS + 1);
	for (int i = 0; i < nrec; i++) {
		uint16_t addr = pick_addr(fuzz_u16(&in));
		const uint8_t *body;
		size_t n = fuzz_take(&in, fuzz_u8(&in), &body);
		uint8_t *pl = fuzz_dup(body, n);
		ingest(&id, &hw, addr, pl, n);
		free(pl);
	}
	/* The family is the one that the harness's hw table gives for the last 0x0600
	 * payload that ingest accepted, and UNKNOWN with no such payload or with a
	 * payload that no row names.
	 * contract: include/reac/reac_box_facts.h:29-35, :37-40
	 * mutant: src/reac_box_facts.c:17 `REAC_BOX_FAMILY_S1608` -> `REAC_BOX_FAMILY_S4000S`
	 * input: catalogue-s1608 */
	if (reac_box_family_of(&id) != family_of_hw(&hw))
		abort();

	uint8_t fam_raw = fuzz_u8(&in);
	int in_ch = fuzz_u8(&in), out_ch = fuzz_u8(&in);
	size_t cap_fw = fuzz_u8(&in) % 16, cap_ver = fuzz_u8(&in) % 32;
	size_t cap_name = fuzz_u8(&in) % 40, cap_tok = fuzz_u8(&in) % 40,
	       cap_disp = fuzz_u8(&in) % 64;
	uint8_t row = fuzz_u8(&in);
	uint16_t any_fw = fuzz_u16(&in);

	/* The formatters at an input-chosen capacity, on the decoded firmware and on any
	 * value at all. */
	char *s = buf_of(cap_fw);
	check_str(reac_identity_fw_str(id.fw_milli, s, cap_fw), s, cap_fw);
	check_str(reac_identity_fw_str(any_fw, s, cap_fw), s, cap_fw);
	free(s);
	s = buf_of(cap_ver);
	check_str(reac_identity_reac_ver_str(id.reac_version_major, id.reac_version_minor,
	                                     id.reac_version_patch, s, cap_ver), s, cap_ver);
	free(s);

	/* Any value at the documented capacity: the whole part (a two-digit whole
	 * part is carried, not truncated), ".", and three digits. */
	{
		char f[REAC_IDENTITY_FW_STR_CAP], ef[16];
		size_t en = 0;
		put_dec(ef, &en, any_fw / 1000u, 1);
		ef[en++] = '.';
		put_dec(ef, &en, any_fw % 1000u, 3);
		ef[en] = '\0';
		int w = reac_identity_fw_str(any_fw, f, sizeof f);
		/* mutant: src/reac_identity.c:105 `whole >= 10` -> `whole >= 100`
		 * input: refusals-and-small-buffers
		 * mutant: src/reac_identity.c:98 `cap < REAC_IDENTITY_FW_STR_CAP` -> `cap <= REAC_IDENTITY_FW_STR_CAP`
		 * input: odd-width */
		if (w < 0 || (size_t)w != en || memcmp(f, ef, en + 1) != 0)
			abort();
	}

	/* The family is the identity page's verdict, or any value the input names. */
	enum reac_box_family fam = (fam_raw & 0x80) ? (enum reac_box_family)(fam_raw & 0x7f)
	                                            : reac_box_family_of(&id);
	/* mutant: src/reac_box_facts.c:35 `return "S-1608";` -> `return 0;`
	 * input: catalogue-s1608 */
	if (!reac_box_family_stem(fam))
		abort();
	const char *said = id.has_model_name ? id.model_name : NULL;
	char *nm = buf_of(cap_name), *tk = buf_of(cap_tok), *dp = buf_of(cap_disp);
	/* mutant: src/reac_box_facts.c:77 `return -1;` -> `return 0;`
	 * input: catalogue-s1608 */
	if (reac_box_name(fam, said, 8, 8, NULL, 8, tk, cap_tok, dp, cap_disp) != -1)
		abort();
	int r = reac_box_name(fam, said, in_ch, out_ch, nm, cap_name, tk, cap_tok, dp, cap_disp);
	/* mutant: src/reac_box_facts.c:126 `return 0;` -> `return 1;`
	 * input: catalogue-s1608 */
	if (r != 0 && r != -1)
		abort();
	int wok = width_ok(in_ch) && width_ok(out_ch) && !(in_ch == 0 && out_ch == 0);
	/* A bad width is refused.
	 * mutant: src/reac_box_facts.c:78 `!reac_box_width_ok(in_ch)` -> `0`
	 * input: odd-width */
	if (!wok && r != -1)
		abort();

	/* The expected strings (reac_box_facts.h:46-60). The stem is at most 16
	 * bytes, so the name is at most 21 and the display at most 38. */
	char exp_nm[32], exp_dp[64];
	exp_nm[0] = exp_dp[0] = '\0';
	if (wok) {
		const char *stem = (said && said[0]) ? said : stem_of((int)fam);
		char w4[8];
		size_t n4 = 0, ln = 0, ld = 0;
		put_dec(w4, &n4, (unsigned)in_ch, 2);
		put_dec(w4, &n4, (unsigned)out_ch, 2);
		w4[n4] = '\0';
		put_str(exp_nm, &ln, stem);
		if (!(ln >= 4 && memcmp(exp_nm + ln - 4, w4, 4) == 0)) {
			exp_nm[ln++] = '-';
			put_str(exp_nm, &ln, w4);
		}
		exp_nm[ln] = '\0';
		put_str(exp_dp, &ld, exp_nm);
		put_str(exp_dp, &ld, " (");
		put_dec(exp_dp, &ld, (unsigned)in_ch, 1);
		put_str(exp_dp, &ld, " in / ");
		put_dec(exp_dp, &ld, (unsigned)out_ch, 1);
		put_str(exp_dp, &ld, " out)");
		exp_dp[ld] = '\0';
		size_t lt = ln - (memchr(exp_nm, '-', ln) ? 1 : 0);
		int fits = ln < cap_name && lt < cap_tok && ld < cap_disp;
		/* Good widths and room for each string: the name is made.
		 * mutant: src/reac_box_facts.c:79 `(in_ch == 0 && out_ch == 0)` -> `1`
		 * input: catalogue-s1608 */
		if (fits && r != 0)
			abort();
		/* A buffer with no room for its string and its NUL: refused.
		 * mutant: src/reac_box_facts.c:121 `nb.n >= name_len` -> `nb.n > name_len`
		 * input: s1608-name-cap-equal-length
		 * mutant: src/reac_box_facts.c:121 `tb.n >= token_len` -> `tb.n > token_len`
		 * input: s1608-token-cap-equal-length
		 * mutant: src/reac_box_facts.c:121 `db.n >= display_len` -> `db.n > display_len`
		 * input: s1608-display-cap-equal-length */
		if (!fits && r != -1)
			abort();
	}
	if (r == 0) {
		check_str((int)strlen(nm), nm, cap_name);
		check_str((int)strlen(tk), tk, cap_tok);
		check_str((int)strlen(dp), dp, cap_disp);
		/* The name is the expected name.
		 * mutant: src/reac_box_facts.c:86 `sb_dec(&wb, in_ch, 2);` -> `sb_dec(&wb, out_ch, 2);`
		 * input: catalogue-s1608 */
		if (strcmp(nm, exp_nm) != 0)
			abort();
		/* The display is the expected display.
		 * mutant: src/reac_box_facts.c:114 `sb_dec(&db, in_ch, 1);` -> `sb_dec(&db, out_ch, 1);`
		 * input: catalogue-s1608 */
		if (strcmp(dp, exp_dp) != 0)
			abort();
		/* token = name lower-cased, its first '-' dropped */
		size_t j = 0;
		int dropped = 0;
		for (size_t i = 0; nm[i]; i++) {
			char c = nm[i];
			if (c == '-' && !dropped) { dropped = 1; continue; }
			if (c >= 'A' && c <= 'Z') c = (char)(c - 'A' + 'a');
			/* mutant: src/reac_box_facts.c:105 `c - 'A' + 'a'` -> `c`
			 * input: catalogue-s1608 */
			if (tk[j++] != c)
				abort();
		}
		/* The token ends where the name ends.
		 * mutant: src/reac_box_facts.c:108 `tk[tb.n] = 0;` -> `tk[tb.n++] = 'x'; tk[tb.n] = 0;`
		 * input: catalogue-s1608 */
		if (tk[j] != '\0')
			abort();
		size_t count = 0;
		const struct reac_box_model *cat = reac_box_catalogue(&count);
		const struct reac_box_model *e = count ? &cat[row % count] : NULL;
		int mask = reac_box_catalogue_defect(e, in_ch, out_ch, dp);
		int exp_mask = 0;
		if (e && (e->in_ch != in_ch || e->out_ch != out_ch))
			exp_mask |= REAC_BOX_DEFECT_WIDTH;
		if (e && e->display && strcmp(e->display, dp) != 0)
			exp_mask |= REAC_BOX_DEFECT_NAME;
		/* WIDTH exactly when the widths differ, NAME exactly when the display
		 * differs, and no other bit.
		 * mutant: src/reac_box_facts.c:132 `!entry` -> `!entry || 1`
		 * input: catalogue-s4000s
		 * mutant: src/reac_box_facts.c:136 `mask |= REAC_BOX_DEFECT_WIDTH;` -> ``
		 * input: catalogue-s4000s
		 * mutant: src/reac_box_facts.c:138 `mask |= REAC_BOX_DEFECT_NAME;` -> ``
		 * input: catalogue-s4000s
		 * mutant: src/reac_box_facts.c:139 `return mask;` -> `return mask | 4;`
		 * input: catalogue-s1608 */
		if (mask != exp_mask)
			abort();
	}
	free(dp);
	free(tk);
	free(nm);
	return 0;
}
