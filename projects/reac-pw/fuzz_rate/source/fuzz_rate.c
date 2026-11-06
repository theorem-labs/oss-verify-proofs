// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>

/* libFuzzer harness: THE `reac.cfg.rate` CONTROL WRITE (src/reac_rate_cfg.c), the pace a
 * controller asks the master node for, and the decision that accepts or refuses it.
 *
 * Input:  [0] flags: bit 0 hands the parse a NULL object, bit 1 decides for a slave;
 *         [1] the drivable mask the decision is given;
 *         [2] the length of the buffer the drivable list is written into, mod 24;
 *         [3..6] u32 LE: a second rate, decided as well as the parsed one;
 *         [7..] the Props object, as fuzz/pod.h reads it.
 *
 * The expectations come from the record fuzz/pod.h keeps of the object, and from the
 * header: the value of the first pair keyed "reac.cfg.rate" is the rate when it is an Int
 * or a Float with a nearest integer in an int's range, and malformed otherwise
 * (src/reac_rate_cfg.h:83-92); the closed list is 44100, 48000 and 96000 and a slave has
 * no rate of its own (src/reac_rate_cfg.h:59-60, 76-81).
 *
 * Properties, each an abort():
 *   - a write with no rate key is 0, and the caller's rate is left as it was;
 *   - a usable rate is 1 and the rate the pod carries;
 *   - an unusable one, or no Props object, is -1, the caller's rate left as it was;
 *   - the decision refuses a slave, then a rate off the closed list, then a rate the
 *     segment cannot drive, and accepts the rest;
 *   - each refusal has its published code;
 *   - a rate's bit, its membership of the closed list and the best drivable rate follow
 *     the closed list;
 *   - and the drivable list is the drivable rates, ascending, cut to the buffer. */
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "reac_rate_cfg.h"
#include <reac/reac_cfg.h>

#include "fuzz.h"
#include "pod.h"

/* contract: facts/reac_facts.h:1644-1650 (REAC_SAMPLE_RATE_48K, _96K, _44K1) */
static const int closed_list[3] = { 44100, 48000, 96000 };
/* contract: libreac 1.9.0 include/reac/reac_cfg.h:107-112 (one bit per closed-list rate, 44100 first) */
static unsigned bit_of(int hz)
{
	for (int i = 0; i < 3; i++)
		if (hz == closed_list[i])
			return 1u << i;
	return 0;
}

/* contract: libreac 1.9.0 include/reac/reac_cfg.h:115-133 (the refusal codes) */
static const char *code_of(enum reac_rate_refuse r)
{
	switch (r) {
	case REAC_RATE_REFUSE_NOT_CLOSED: return "not_closed";
	case REAC_RATE_REFUSE_NOT_DRIVABLE: return "not_drivable";
	case REAC_RATE_REFUSE_ROLE_SLAVE: return "role_slave";
	case REAC_RATE_REFUSE_MALFORMED: return "malformed";
	default: return "none";
	}
}

/* What the parse owes: 1 and the rate, 0, or -1. */
static int expect_rate(const struct pod_props *pp, int null, int *hz)
{
	if (null || !pp->is_props)
		return -1;
	int at = 0, v;
	const char *k;
	while (pp->params_struct && (v = pod_next_pair(pp, &at, &k)) >= 0) {
		if (strcmp(k, REAC_CFG_RATE_PROP) != 0)
			continue;
		int32_t i;
		float f;
		long long near;
		if (pod_int(&pp->ent[v], &i)) {
			*hz = i;
			return 1;
		}
		if (pod_float(&pp->ent[v], &f) && pod_nearest(f, INT32_MIN, INT32_MAX, &near)) {
			*hz = (int)near;
			return 1;
		}
		return -1;
	}
	return 0;
}

static enum reac_rate_refuse expect_decide(enum reac_role role, int hz, unsigned mask)
{
	if (role == REAC_ROLE_SLAVE)
		return REAC_RATE_REFUSE_ROLE_SLAVE;
	if (!bit_of(hz))
		return REAC_RATE_REFUSE_NOT_CLOSED;
	if (!(mask & bit_of(hz)))
		return REAC_RATE_REFUSE_NOT_DRIVABLE;
	return REAC_RATE_REFUSE_NONE;
}

/* The drivable list of `mask`, and whether the reader's answer is it: the length of the
 * whole list, and in a buffer of `buflen` as much of it as fits before a NUL, or the
 * buffer untouched when it has no room at all. */
static int csv_holds(const char *buf, size_t buflen, size_t len, unsigned mask)
{
	char want[40];
	size_t n = 0;
	for (int i = 0; i < 3; i++) {
		if (!(mask & (1u << i)))
			continue;
		int v = closed_list[i];
		char d[8];
		int k = 0;
		do {
			d[k++] = (char)('0' + v % 10);
			v /= 10;
		} while (v);
		if (n)
			want[n++] = ',';
		while (k)
			want[n++] = d[--k];
	}
	if (len != n)
		return 0;
	if (buflen == 0)
		return (unsigned char)buf[0] == 0x5a;
	size_t c = n < buflen - 1 ? n : buflen - 1;
	return memcmp(buf, want, c) == 0 && buf[c] == '\0';
}

static FUZZ_NOINLINE void check_absent(int rc, int hz)
{
	/* A Props write that carries no rate key (only volume, head-amp or nothing) is 0, and
	 * the caller's variable is not written.
	 * contract: src/reac_rate_cfg.h:88-89 (0 if the key is simply absent)
	 * mutant: src/reac_rate_cfg.c:124 `return 0;` -> `return -1;`
	 * input: params-not-a-struct
	 * mutant: src/reac_rate_cfg.c:142 `strcmp(k, REAC_CFG_PROP_RATE) != 0` -> `strncmp(k, REAC_CFG_PROP_RATE, 12) != 0`
	 * input: near-keys */
	if (rc != 0 || hz != 0x5a5a5a5a)
		abort();
}

static FUZZ_NOINLINE void check_rate(int rc, int hz, int want)
{
	/* A rate key with an Int, or a Float with a nearest integer an int holds, is 1 and
	 * that rate, the first such key's.
	 * contract: src/reac_rate_cfg.h:85-87 (accepted as Int or Float; 1 and *out_hz)
	 * mutant: src/reac_rate_cfg.c:103 `*out = (int)i;` -> `*out = (int)i + 1;`
	 * input: rate-48000
	 * mutant: src/reac_float_near.h:31 `r--;` -> ``
	 * input: rate-float-negative
	 * mutant: src/reac_rate_cfg.c:140 `key = NULL;` -> ``
	 * input: rate-after-other-key */
	if (rc != 1 || hz != want)
		abort();
}

static FUZZ_NOINLINE void check_malformed(int rc, int hz)
{
	/* A rate key whose value is no number an int holds (a Bool, a String, NaN, an
	 * infinity, a Float past int), or a pod that is not a Props object, is -1, and the
	 * caller's variable is not written.
	 * contract: src/reac_rate_cfg.h:89-91 (-1 if not readable as a number, or not an
	 * Object pod), src/reac_float_near.h:8-10
	 * mutant: src/reac_float_near.h:27 `d >= (double)lo &&` -> ``
	 * input: rate-float-huge
	 * mutant: src/reac_rate_cfg.c:112 `return -1;` -> `return 0;`
	 * input: rate-bool
	 * mutant: src/reac_rate_cfg.c:117 `SPA_TYPE_OBJECT_Props` -> `SPA_TYPE_OBJECT_PropInfo`
	 * input: not-props-rate */
	if (rc != -1 || hz != 0x5a5a5a5a)
		abort();
}

static FUZZ_NOINLINE void check_decide(enum reac_rate_refuse got, enum reac_rate_refuse want)
{
	/* A slave is refused whatever it asks; then a rate off the closed list; then one
	 * outside the drivable mask; every other rate is accepted.
	 * contract: src/reac_rate_cfg.h:59-60, 76-81, libreac 1.9.0 include/reac/reac_cfg.h:124-126
	 * mutant: src/reac_rate_cfg.c:87 `drivable_mask & reac_rate_bit(requested_hz)` -> `drivable_mask`
	 * input: rate-not-drivable
	 * mutant: src/reac_rate_cfg.c:83 `role == REAC_ROLE_SLAVE` -> `0`
	 * input: slave-asks-48000
	 * mutant: src/reac_rate_cfg.c:26 `hz == REAC_SAMPLE_RATE_44K1 ||` -> ``
	 * input: rate-44100 */
	if (got != want)
		abort();
}

static FUZZ_NOINLINE void check_code(const char *got, enum reac_rate_refuse r)
{
	/* Each refusal publishes its own code from the shared vocabulary.
	 * contract: src/reac_rate_cfg.h:56-57, libreac 1.9.0 include/reac/reac_cfg.h:145-153 (the code for each refusal)
	 * mutant: src/reac_rate_cfg.c:21 `return codes[r];` -> `return codes[REAC_RATE_REFUSE_NONE];`
	 * input: rate-not-drivable
	 * mutant: src/reac_rate_cfg.c:21 `return codes[r];` -> `return codes[REAC_RATE_REFUSE_NOT_CLOSED];`
	 * input: slave-asks-48000 */
	if (strcmp(got, code_of(r)) != 0)
		abort();
}

static FUZZ_NOINLINE void check_list(int hz, unsigned bit, int closed, unsigned mask, int best)
{
	/* A rate's bit is its place in the closed list and 0 off it, it is in the list
	 * exactly when it has a bit, and the best drivable rate is the highest whose bit the
	 * mask sets, 0 for none.
	 * contract: src/reac_rate_cfg.h:59-69
	 * mutant: src/reac_rate_cfg.c:35 `REAC_RATE_BIT_96000` -> `REAC_RATE_BIT_48000`
	 * input: rate-96000
	 * mutant: src/reac_rate_cfg.c:43 `REAC_RATE_BIT_96000` -> `REAC_RATE_BIT_48000`
	 * input: rate-not-drivable */
	if (bit != bit_of(hz) || closed != (bit_of(hz) != 0) ||
	    best != (mask & 4 ? 96000 : mask & 2 ? 48000 : mask & 1 ? 44100 : 0))
		abort();
}

static FUZZ_NOINLINE void check_csv(const char *buf, size_t buflen, size_t len, unsigned mask)
{
	/* The drivable list is the drivable rates in ascending order, comma separated; the
	 * length returned is the whole list's, and the buffer holds as much of it as fits
	 * before its NUL.
	 * contract: src/reac_rate_cfg.h:71-74 (ascending CSV; snprintf convention)
	 * mutant: src/reac_rate_cfg.c:60 `len ? "," : ""` -> `""`
	 * input: rate-not-drivable
	 * mutant: src/reac_rate_cfg.c:70 `: buflen - 1;` -> `: buflen;`
	 * input: rate-48000 */
	if (!csv_holds(buf, buflen, len, mask))
		abort();
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	if (size >= FUZZ_INPUT_MAX)
		return 0;
	struct fuzz_in in = fuzz_in(data, size);
	uint8_t flags = fuzz_u8(&in);
	unsigned mask = fuzz_u8(&in);
	size_t buflen = fuzz_u8(&in) % 24;
	int other = (int)fuzz_u32(&in);
	struct pod_props *pp = malloc(sizeof *pp);
	/* not a property: the harness's own allocation failed */
	if (!pp)
		abort();
	pod_build(&in, pp);
	uint8_t *pod = fuzz_dup(pp->buf, pp->len);
	enum reac_role role = (flags & 2) ? REAC_ROLE_SLAVE : REAC_ROLE_MASTER;

	int hz = 0x5a5a5a5a;
	int rc = reac_rate_prop_parse((flags & 1) ? NULL : (const struct spa_pod *)pod, &hz);
	if (!pp->corrupt) {
		int want = 0;
		int x = expect_rate(pp, flags & 1, &want);
		if (x == 0)
			check_absent(rc, hz);
		else if (x == 1)
			check_rate(rc, hz, want);
		else
			check_malformed(rc, hz);
	}

	/* The decision, the code and the list, for the parsed rate and the input's own. */
	int asked[2] = { rc == 1 ? hz : 48000, other };
	for (int i = 0; i < 2; i++) {
		enum reac_rate_refuse r = reac_rate_cfg_decide(role, asked[i], mask);
		check_decide(r, expect_decide(role, asked[i], mask));
		check_code(reac_rate_refuse_code(r), r);
		check_list(asked[i], reac_rate_bit(asked[i]), reac_rate_is_closed(asked[i]), mask,
		           reac_rate_best_drivable(mask));
	}
	check_code(reac_rate_refuse_code(REAC_RATE_REFUSE_MALFORMED), REAC_RATE_REFUSE_MALFORMED);

	char *buf = malloc(buflen ? buflen : 1);
	/* not a property: the harness's own allocation failed */
	if (!buf)
		abort();
	memset(buf, 0x5a, buflen ? buflen : 1);
	size_t len = reac_rate_drivable_csv(mask, buf, buflen);
	check_csv(buf, buflen, len, mask);

	free(buf);
	free(pod);
	free(pp);
	return 0;
}
