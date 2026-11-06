// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>

/* libFuzzer harness: THE `reac.cfg.role` CONTROL WRITE (src/reac_role_cfg.c), the role a
 * controller asks a segment's node for, and the answer it publishes.
 *
 * Input:  [0] flags: bit 0 hands the parse a NULL object, bit 1 runs the segment as a
 *             slave (the role the answer is worked out against);
 *         [1..] the Props object, as fuzz/pod.h reads it.
 *
 * The expectations come from the record fuzz/pod.h keeps of the object, and from the
 * header: the value of the first pair keyed "reac.cfg.role", an Int or a Float read as
 * its nearest integer, is 0 for the master and 1 for the slave, and anything else is
 * malformed (src/reac_role_cfg.h:92-101); the same role asserted is applied, a
 * different one pending (src/reac_role_cfg.h:80-90).
 *
 * Properties, each an abort():
 *   - a write with no role key is 0, and the caller's role is left as it was;
 *   - 0 is the master and 1 the slave, each 1;
 *   - every other value, or no Props object, is -1, the caller's role left as it was;
 *   - the answer is applied for the running role and pending for the other;
 *   - and each refusal has its published code. */
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "reac_role_cfg.h"
#include <reac/reac_cfg.h>

#include "fuzz.h"
#include "pod.h"

#define ROLE_FLAG_MASTER REAC_CFG_ROLE_MASTER
#define ROLE_FLAG_SLAVE REAC_CFG_ROLE_SLAVE

/* The sentinel the caller's role holds before the parse: neither role. */
#define ROLE_UNSET ((enum reac_role)0x5a)

/* What the parse owes: 1 and the role, 0, or -1. */
static int expect_role(const struct pod_props *pp, int null, enum reac_role *role)
{
	if (null || !pp->is_props)
		return -1;
	int at = 0, v;
	const char *k;
	while (pp->params_struct && (v = pod_next_pair(pp, &at, &k)) >= 0) {
		if (strcmp(k, REAC_CFG_ROLE_PROP) != 0)
			continue;
		int32_t i;
		float f;
		long long flag = -1;
		if (pod_int(&pp->ent[v], &i))
			flag = i;
		else if (!pod_float(&pp->ent[v], &f) || !pod_nearest(f, INT32_MIN, INT32_MAX, &flag))
			return -1;
		if (flag != ROLE_FLAG_MASTER && flag != ROLE_FLAG_SLAVE)
			return -1;
		*role = flag == ROLE_FLAG_MASTER ? REAC_ROLE_MASTER : REAC_ROLE_SLAVE;
		return 1;
	}
	return 0;
}

static FUZZ_NOINLINE void check_absent(int rc, enum reac_role role)
{
	/* A Props write that carries no role key is 0, and the caller's variable is not
	 * written.
	 * contract: src/reac_role_cfg.h:96-97 (0 if the key is simply absent)
	 * mutant: src/reac_role_cfg.c:72 `return 0;` -> `return -1;`
	 * input: params-not-a-struct
	 * mutant: src/reac_role_cfg.c:90 `strcmp(k, REAC_CFG_PROP_ROLE) != 0` -> `strncmp(k, REAC_CFG_PROP_ROLE, 13) != 0`
	 * input: near-role-keys */
	if (rc != 0 || role != ROLE_UNSET)
		abort();
}

static FUZZ_NOINLINE void check_role(int rc, enum reac_role role, enum reac_role want)
{
	/* 0 asks for the master and 1 for the slave, as an Int or as a Float whose nearest
	 * integer it is; the first role key answers.
	 * contract: src/reac_role_cfg.h:94-97 (exactly MASTER or SLAVE: 1 and *out_role)
	 * mutant: src/reac_role_cfg.c:98 `*out_role = REAC_ROLE_MASTER;` -> `*out_role = REAC_ROLE_SLAVE;`
	 * input: role-master
	 * mutant: src/reac_float_near.h:26 `(double)f + 0.5` -> `(double)(f + 0.5f)`
	 * input: role-float-below-half */
	if (rc != 1 || role != want)
		abort();
}

static FUZZ_NOINLINE void check_malformed(int rc, enum reac_role role)
{
	/* A role key whose value is neither 0 nor 1, or no number, or a pod that is not a
	 * Props object, is -1, and the caller's variable is not written.
	 * contract: src/reac_role_cfg.h:98-101 (-1 if not readable as a number or neither
	 * 0 nor 1, or not an Object pod)
	 * mutant: src/reac_role_cfg.c:100 `default: return -1;` -> `default: return 1;`
	 * input: role-two
	 * mutant: src/reac_float_near.h:31 `r--;` -> ``
	 * input: role-float-negative
	 * mutant: src/reac_role_cfg.c:65 `SPA_TYPE_OBJECT_Props` -> `SPA_TYPE_OBJECT_PropInfo`
	 * input: not-props-role */
	if (rc != -1 || role != ROLE_UNSET)
		abort();
}

static FUZZ_NOINLINE void check_answer(int changes, const char *state, enum reac_role cur,
                                       enum reac_role req)
{
	/* The running role asserted again changes nothing and is applied; the other role is
	 * a change, pending until the swap carries it.
	 * contract: src/reac_role_cfg.h:80-90
	 * mutant: src/reac_role_cfg.c:24 `current_role != requested_role` -> `1`
	 * input: role-master
	 * mutant: src/reac_role_cfg.c:36 `REAC_ROLE_STATE_APPLIED` -> `REAC_ROLE_STATE_REESTABLISH_PENDING`
	 * input: role-master */
	if (changes != (cur != req) || strcmp(state, cur != req ? REAC_CFG_ROLE_STATE_PENDING : REAC_CFG_ROLE_STATE_APPLIED) != 0)
		abort();
}

static FUZZ_NOINLINE void check_code(const char *none, const char *malformed)
{
	/* A refusal publishes its code from the shared vocabulary, and no refusal "none".
	 * contract: src/reac_role_cfg.h:77-78, libreac 1.9.0 include/reac/reac_cfg.h:155-167
	 * mutant: src/reac_role_cfg.c:19 `return codes[r];` -> `return codes[REAC_ROLE_REFUSE_NONE];`
	 * input: role-two
	 * mutant: src/reac_role_cfg.c:19 `return codes[r];` -> `return codes[REAC_ROLE_REFUSE_MALFORMED];`
	 * input: role-master */
	if (strcmp(none, "none") != 0 || strcmp(malformed, "malformed") != 0)
		abort();
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	if (size >= FUZZ_INPUT_MAX)
		return 0;
	struct fuzz_in in = fuzz_in(data, size);
	uint8_t flags = fuzz_u8(&in);
	struct pod_props *pp = malloc(sizeof *pp);
	/* not a property: the harness's own allocation failed */
	if (!pp)
		abort();
	pod_build(&in, pp);
	uint8_t *pod = fuzz_dup(pp->buf, pp->len);
	enum reac_role cur = (flags & 2) ? REAC_ROLE_SLAVE : REAC_ROLE_MASTER;

	enum reac_role role = ROLE_UNSET;
	int rc = reac_role_prop_parse((flags & 1) ? NULL : (const struct spa_pod *)pod, &role);
	if (!pp->corrupt) {
		enum reac_role want = ROLE_UNSET;
		int x = expect_role(pp, flags & 1, &want);
		if (x == 0)
			check_absent(rc, role);
		else if (x == 1)
			check_role(rc, role, want);
		else
			check_malformed(rc, role);
	}
	enum reac_role req = rc == 1 ? role : (cur == REAC_ROLE_MASTER ? REAC_ROLE_SLAVE
	                                                               : REAC_ROLE_MASTER);
	check_answer(reac_role_cfg_changes(cur, req), reac_role_cfg_apply_state(cur, req), cur, req);
	check_code(reac_role_refuse_code(REAC_ROLE_REFUSE_NONE),
	           reac_role_refuse_code(REAC_ROLE_REFUSE_MALFORMED));

	free(pod);
	free(pp);
	return 0;
}
