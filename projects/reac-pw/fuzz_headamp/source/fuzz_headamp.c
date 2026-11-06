// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>

/* libFuzzer harness: THE HEAD-AMP CONTROL WRITE (src/reac_headamp_prop.c), the
 * "reac.headamp.<ch>.<param>" cells a controller sets on the master node's Props.
 *
 * Input:  [0] flags: bit 0 hands the reader a NULL object;
 *         [1] the capacity of the cell array, mod 10;
 *         [2..] the Props object, as fuzz/pod.h reads it.
 *
 * The expectations come from the record fuzz/pod.h keeps of the object it wrote and
 * from the head-amp grammar (src/reac_headamp_prop.h:30-32, 62-89): a key under the
 * prefix is a decimal channel, a '.', and one of phantom, pad or sens; a channel past
 * the head-amp channel space or a value its param does not take is OUT_OF_RANGE, a key
 * that addresses no cell is BAD_KEY; the first refusal is the one reported.
 *
 * Properties, each an abort():
 *   - the reader never writes past the capacity it is given;
 *   - what it returns is -1 or a count within that capacity, and its result says the
 *     same count, with at least as many keys;
 *   - every cell it hands on addresses a real cell with a value its param takes;
 *   - it answers -1 exactly for what is not a Props object;
 *   - the cells are the well-formed ones, in order, up to the capacity;
 *   - it counts every key under the prefix it reached, good or bad;
 *   - it reports the first refusal, and none when every key stood;
 *   - and the plain parse returns the count and writes the cells that the parse with a
 *     result returns and writes. */
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "reac_headamp_prop.h"

#include "fuzz.h"
#include "pod.h"

/* contract: src/reac_headamp_prop.h:32 (the key prefix) */
#define HA_PREFIX "reac.headamp."
/* contract: facts/reac_facts.h:1080 (REAC_HEADAMP_CH_SPAN 0x30: the head-amp channel
 * space, 0x00..0x2f) */
#define HA_CHANNELS 0x30
/* contract: facts/reac_facts.h:1074 (REAC_HEADAMP_SENS_MAX 0x37) */
#define HA_SENS_MAX 0x37
/* contract: libreac 1.8.0 include/reac/reac_ctrlblk.h:759-761 (phantom 0, pad 1, sens 2) */
#define HA_PHANTOM 0
#define HA_PAD     1
#define HA_SENS    2

#define CAP_MAX 10

struct cell {
	int ch, param, value;
};

struct expect {
	int rc;
	struct cell cell[CAP_MAX];
	int n;
	int keys;
	enum reac_headamp_refuse refusal;
};

/* strtol's reading of a decimal channel at the start of s, as C defines it: blanks, a
 * sign, then one digit or more. Returns the characters read, 0 when there is no digit;
 * *big is set when the value is past any channel. */
static size_t read_channel(const char *s, long *v, int *big)
{
	size_t i = 0;
	while (s[i] == ' ' || s[i] == '\t' || s[i] == '\n' || s[i] == '\v' || s[i] == '\f' ||
	       s[i] == '\r')
		i++;
	int neg = 0;
	if (s[i] == '+' || s[i] == '-')
		neg = s[i++] == '-';
	size_t d = i;
	long acc = 0;
	*big = 0;
	while (s[i] >= '0' && s[i] <= '9') {
		if (acc > 1000000)
			*big = 1;
		else
			acc = acc * 10 + (s[i] - '0');
		i++;
	}
	if (i == d)
		return 0;
	*v = neg ? -acc : acc;
	return i;
}

/* The value a pod gives a param, or -1 for none: a Bool is 0 or 1, an Int is itself
 * when it fits a byte, a Float its nearest integer when that fits a byte. */
static int cell_value(const struct pod_ent *e)
{
	int b;
	int32_t i;
	float f;
	long long near;
	if (pod_bool(e, &b))
		return b;
	if (pod_int(e, &i))
		return i >= 0 && i <= 255 ? (int)i : -1;
	if (pod_float(e, &f))
		return pod_nearest(f, 0, 255, &near) ? (int)near : -1;
	return -1;
}

static void expect_of(const struct pod_props *pp, int null, int cap, struct expect *x)
{
	memset(x, 0, sizeof *x);
	x->refusal = REAC_HEADAMP_REFUSE_NONE;
	if (null || !pp->is_props) {
		x->rc = -1;
		return;
	}
	int at = 0, v;
	const char *k;
	while (pp->params_struct && (v = pod_next_pair(pp, &at, &k)) >= 0) {
		if (strncmp(k, HA_PREFIX, strlen(HA_PREFIX)) != 0)
			continue;
		x->keys++;
		const char *rest = k + strlen(HA_PREFIX);
		enum reac_headamp_refuse bad = REAC_HEADAMP_REFUSE_NONE;
		long ch = 0;
		int big = 0, param = -1, value = -1;
		size_t used = read_channel(rest, &ch, &big);
		if (!used || rest[used] != '.') {
			bad = REAC_HEADAMP_REFUSE_BAD_KEY;
		} else {
			const char *name = rest + used + 1;
			param = !strcmp(name, "phantom") ? HA_PHANTOM : !strcmp(name, "pad") ? HA_PAD
			      : !strcmp(name, "sens") ? HA_SENS : -1;
			if (param < 0)
				bad = REAC_HEADAMP_REFUSE_BAD_KEY;
			else if (big || ch < 0 || ch >= HA_CHANNELS)
				bad = REAC_HEADAMP_REFUSE_OUT_OF_RANGE;
		}
		if (bad == REAC_HEADAMP_REFUSE_NONE) {
			value = cell_value(&pp->ent[v]);
			if (value < 0 || value > (param == HA_SENS ? HA_SENS_MAX : 1))
				bad = REAC_HEADAMP_REFUSE_OUT_OF_RANGE;
		}
		if (bad != REAC_HEADAMP_REFUSE_NONE) {
			if (x->refusal == REAC_HEADAMP_REFUSE_NONE)
				x->refusal = bad;
			continue;
		}
		if (x->n >= cap)
			break;
		x->cell[x->n].ch = (int)ch;
		x->cell[x->n].param = param;
		x->cell[x->n].value = value;
		x->n++;
	}
	x->rc = x->n;
}

/* Each of the `rc` cells addresses the channel space with a param it has and a value
 * that param takes. */
static int cells_valid(const struct reac_headamp_setting *out, int rc)
{
	for (int i = 0; i < rc; i++) {
		int top = out[i].param == HA_SENS ? HA_SENS_MAX : 1;
		if (out[i].ch >= HA_CHANNELS || out[i].param > HA_SENS || out[i].value > top)
			return 0;
	}
	return 1;
}

/* The return is the expected count and the cells are the expected ones. */
static int cells_equal(const struct reac_headamp_setting *out, int rc, const struct expect *x)
{
	if (rc != x->rc)
		return 0;
	for (int i = 0; i < rc; i++)
		if (out[i].ch != x->cell[i].ch || out[i].param != x->cell[i].param ||
		    out[i].value != x->cell[i].value)
			return 0;
	return 1;
}

static FUZZ_NOINLINE void check_no_overrun(const struct reac_headamp_setting *guard)
{
	/* The reader writes no cell past the capacity it was given: the cell after the last is
	 * the harness's own, and it is as the harness left it.
	 * contract: src/reac_headamp_prop.h:89 (never writes past `max`)
	 * mutant: src/reac_headamp_prop.c:169 `n >= max` -> `n > max`
	 * input: cap-one-two-cells */
	if (guard->ch != 0xa5 || guard->param != 0xa5 || guard->value != 0xa5)
		abort();
}

static FUZZ_NOINLINE void check_count(int rc, int cap, const struct reac_headamp_prop_result *res)
{
	/* The return is -1 or a count from 0 to the capacity, and a result says that count,
	 * with at least as many head-amp keys seen as cells accepted.
	 * contract: src/reac_headamp_prop.h:79-80, 88-89 (n, keys; 0..max or -1)
	 * mutant: src/reac_headamp_prop.c:177 `res->n = n;` -> `res->n = keys;`
	 * input: cells-and-refusals
	 * mutant: src/reac_headamp_prop.c:174 `n++;` -> `n += 2;`
	 * input: cap-one-two-cells */
	if (rc < -1 || rc > cap || (rc >= 0 && (res->n != rc || res->keys < rc)))
		abort();
}

static FUZZ_NOINLINE void check_cells_valid(const struct reac_headamp_setting *out, int rc)
{
	/* Every cell handed on addresses a cell of the channel space with a param it has, and a
	 * value that param takes: 0 or 1 for phantom and pad, 0 to the last sens step.
	 * contract: src/reac_headamp_prop.h:12-14 (0/1 for phantom and pad, 0..0x37 for sens),
	 * :74-76 (a channel past the space is refused)
	 * mutant: src/reac_headamp_prop.c:80 `c >= REAC_HEADAMP_MAX_CH` -> `c > REAC_HEADAMP_MAX_CH`
	 * input: channel-48
	 * mutant: src/reac_headamp_prop.c:94 `value <= 1` -> `value <= 2`
	 * input: phantom-two */
	if (!cells_valid(out, rc))
		abort();
}

static FUZZ_NOINLINE void check_object(int rc, const struct reac_headamp_prop_result *res,
                                       const struct expect *x)
{
	/* -1 exactly for a NULL pod or one that is not a Props object, and then a result that
	 * says nothing was seen; a Props object without a params Struct is 0 cells, not an
	 * error.
	 * contract: src/reac_headamp_prop.h:88-89 (-1 if props is NULL or not an Object pod)
	 * mutant: src/reac_headamp_prop.c:117 `res->keys = 0;` -> ``
	 * input: not-props
	 * mutant: src/reac_headamp_prop.c:120 `SPA_TYPE_OBJECT_Props` -> `SPA_TYPE_OBJECT_PropInfo`
	 * input: cells-and-refusals
	 * mutant: src/reac_headamp_prop.c:127 `return 0;` -> `return -1;`
	 * input: params-not-a-struct */
	if ((rc == -1) != (x->rc == -1) ||
	    (rc == -1 && (res->n || res->keys || res->refusal != REAC_HEADAMP_REFUSE_NONE)))
		abort();
}

static FUZZ_NOINLINE void check_cells(const struct reac_headamp_setting *out, int rc,
                                      const struct expect *x)
{
	/* The cells are exactly the well-formed ones, in the order written, each with the
	 * channel, the param and the value its key and pod spell, up to the capacity.
	 * contract: src/reac_headamp_prop.h:84-89 (every entry parsed into out, in order)
	 * mutant: src/reac_headamp_prop.c:173 `out[n].value = value;` -> `out[n].value = 1;`
	 * input: cells-and-refusals
	 * mutant: src/reac_headamp_prop.c:96 `value <= REAC_HEADAMP_SENS_MAX` -> `value < REAC_HEADAMP_SENS_MAX`
	 * input: sens-edges
	 * mutant: src/reac_float_near.h:27 `d < (double)hi + 1.0` -> `d <= (double)hi + 1.0`
	 * input: sens-edges
	 * mutant: src/reac_headamp_prop.c:74 `10)` -> `16)`
	 * input: hex-channel
	 * mutant: src/reac_headamp_prop.c:31 `b ? 1 : 0` -> `0`
	 * input: cells-and-refusals
	 * mutant: src/reac_headamp_prop.c:35 `i > 255` -> `i > 256`
	 * input: phantom-256 */
	if (!cells_equal(out, rc, x))
		abort();
}

static FUZZ_NOINLINE void check_keys(const struct reac_headamp_prop_result *res,
                                     const struct expect *x)
{
	/* Every key under the prefix the walk reached is counted, the refused ones too: a
	 * write that was attempted and dropped is still a write.
	 * contract: src/reac_headamp_prop.h:66-69 (`keys` counts every key under the prefix)
	 * mutant: src/reac_headamp_prop.c:153 `keys++;` -> ``
	 * input: refused-only */
	if (res->keys != x->keys)
		abort();
}

static FUZZ_NOINLINE void check_refusal(const struct reac_headamp_prop_result *res,
                                        const struct expect *x)
{
	/* The refusal reported is the FIRST thing wrong with a key, and NONE only when every
	 * key stood.
	 * contract: src/reac_headamp_prop.h:68-77 (the FIRST refusal; BAD_KEY and OUT_OF_RANGE)
	 * mutant: src/reac_headamp_prop.c:164 `refusal == REAC_HEADAMP_REFUSE_NONE` -> `1`
	 * input: refusal-order
	 * mutant: src/reac_headamp_prop.c:79 `return REAC_HEADAMP_REFUSE_BAD_KEY;` -> `return REAC_HEADAMP_REFUSE_OUT_OF_RANGE;`
	 * input: refusal-order */
	if (res->refusal != x->refusal)
		abort();
}

/* The first n cells of a and b hold the same channel, param and value, field by field. */
static int cells_same(const struct reac_headamp_setting *a, const struct reac_headamp_setting *b,
                      int n)
{
	for (int i = 0; i < n; i++)
		if (a[i].ch != b[i].ch || a[i].param != b[i].param || a[i].value != b[i].value)
			return 0;
	return 1;
}

static FUZZ_NOINLINE void check_plain(int plain, int rc, const struct reac_headamp_setting *out,
                                      const struct reac_headamp_setting *first)
{
	/* The parse without a result is the same parse: the same count, and the same cells,
	 * field by field, as the parse with one wrote.
	 * contract: src/reac_headamp_prop.h:94-96 (the same parse, discarding what it saw)
	 * mutant: src/reac_headamp_prop.c:105 `out, max, NULL` -> `out, max - 1, NULL`
	 * input: cap-one-two-cells
	 * mutant: src/reac_headamp_prop.c:173 `= value;` -> `= res ? value : 0;`
	 * input: sens-edges */
	if (plain != rc || !cells_same(out, first, rc))
		abort();
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	if (size >= FUZZ_INPUT_MAX)
		return 0;
	struct fuzz_in in = fuzz_in(data, size);
	int null = fuzz_u8(&in) & 1;
	int cap = fuzz_u8(&in) % CAP_MAX;
	struct pod_props *pp = malloc(sizeof *pp);
	/* not a property: the harness's own allocation failed */
	if (!pp)
		abort();
	pod_build(&in, pp);
	uint8_t *pod = fuzz_dup(pp->buf, pp->len);

	/* The cells the reader may write, and one guard cell after them. */
	struct reac_headamp_setting *out = malloc((size_t)(cap + 1) * sizeof *out);
	/* not a property: the harness's own allocation failed */
	if (!out)
		abort();
	memset(out, 0xa5, (size_t)(cap + 1) * sizeof *out);
	struct reac_headamp_prop_result res;
	memset(&res, 0x5a, sizeof res);
	int rc = reac_headamp_prop_parse_result(null ? NULL : (const struct spa_pod *)pod, out,
	                                        cap, &res);
	check_no_overrun(&out[cap]);
	check_count(rc, cap, &res);
	check_cells_valid(out, rc);
	if (!pp->corrupt) {
		struct expect x;
		expect_of(pp, null, cap, &x);
		check_object(rc, &res, &x);
		check_cells(out, rc, &x);
		if (rc >= 0) {
			check_keys(&res, &x);
			check_refusal(&res, &x);
		}
	}
	/* the cells of the first parse, before the plain parse writes over them */
	struct reac_headamp_setting *first =
		(struct reac_headamp_setting *)fuzz_dup(out, (size_t)(rc > 0 ? rc : 0) * sizeof *out);
	memset(out, 0xa5, (size_t)(cap + 1) * sizeof *out);
	int plain = reac_headamp_prop_parse(null ? NULL : (const struct spa_pod *)pod, out, cap);
	check_plain(plain, rc, out, first);

	free(first);
	free(out);
	free(pod);
	free(pp);
	return 0;
}
