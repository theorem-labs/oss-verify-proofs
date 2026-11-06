// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>

/* libFuzzer harness: THE CATCH-UP BUDGET UNDER ETF (src/reac_qdisc.c,
 * reac_qdisc_etf_catchup_slots), the one arithmetic reac_qdisc.c derives from the
 * pacer's lead and the qdisc's delta.
 *
 * The etf counter read the file used to carry is libreac's reac_etf_qdisc_stats_read
 * since 1.0.42 (ONE HOME); libreac's fuzz_qdisc drives it over a fake rtnetlink kernel,
 * and tests/reac-code-conformance.py refuses an RTM_GETQDISC request built here.
 *
 * Input:  [0] budgets, mod 8; then each budget [u16 lead_us][u8 fps selector].
 *
 * Property, an abort(): the budget is the lead past the qdisc's delta, in slots at fps,
 * rounded down, at least 1 and at most 1000000; no frame rate is 1. */
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

#include "reac_qdisc.h"

#include "fuzz.h"

/* reac_qdisc.c's policy half (arm, disarm, release) calls libreac-transport, which no
 * harness links. This harness never calls that half; these stand-ins only let the
 * file link, and answer as a host with no qdisc support would. */
#include <errno.h>
#include <reac/transport/reac_etf_qdisc.h>
enum reac_etf_qdisc_state reac_etf_qdisc_state(int ifindex, char *root_kind, size_t cap)
{
	(void)ifindex;
	if (root_kind && cap)
		root_kind[0] = '\0';
	return REAC_ETF_QDISC_UNREADABLE;
}

int reac_etf_qdisc_install(int ifindex, uint32_t delta_ns)
{
	(void)ifindex;
	(void)delta_ns;
	return -EOPNOTSUPP;
}

int reac_etf_qdisc_remove(int ifindex)
{
	(void)ifindex;
	return -EOPNOTSUPP;
}

const char *reac_etf_qdisc_fix(int err)
{
	(void)err;
	return "";
}

/* contract: libreac 1.10.0 include/reac/transport/reac_etf_qdisc.h:42 (the qdisc's delta,
 * 300000 ns) */
#define ETF_DELTA_US  300u

#define BUDGETS_MAX 7

/* The catch-up budget the header states. */
static int slots_of(unsigned lead_us, int fps)
{
	if (fps <= 0)
		return 1;
	unsigned long long usable = lead_us > ETF_DELTA_US ? lead_us - ETF_DELTA_US : 0;
	unsigned long long n = usable * (unsigned long long)fps / 1000000ull;
	return n < 1 ? 1 : n > 1000000ull ? 1000000 : (int)n;
}

static FUZZ_NOINLINE void check_slots(int got, unsigned lead_us, int fps)
{
	/* The catch-up budget is the lead past the qdisc's delta, in slots at fps, rounded
	 * down, at least 1 and at most 1000000; no frame rate is 1.
	 * contract: src/reac_qdisc.h:108-129
	 * mutant: src/reac_qdisc.c:178 `lead_us - delta_us` -> `lead_us`
	 * input: lead-2500-at-8000
	 * mutant: src/reac_qdisc.c:183 `if (n < 1)` -> `if (n < 0)`
	 * input: lead-inside-delta
	 * mutant: src/reac_qdisc.c:175 `if (fps <= 0)` -> `if (0)`
	 * input: negative-rate
	 * mutant: src/reac_qdisc.c:185 `if (n > 1000000ull)` -> `if (0)`
	 * input: lead-max-at-max-rate */
	if (got != slots_of(lead_us, fps))
		abort();
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	if (size >= FUZZ_INPUT_MAX)
		return 0;
	struct fuzz_in in = fuzz_in(data, size);
	int budgets = fuzz_u8(&in) % (BUDGETS_MAX + 1);
	static const int fps[] = { 8000, 4000, 0, -1, 96000, 2147483647 };
	for (int b = 0; b < budgets; b++) {
		unsigned lead_us = fuzz_u16(&in);
		int f = fps[fuzz_u8(&in) % 6];
		check_slots(reac_qdisc_etf_catchup_slots(lead_us, f), lead_us, f);
	}
	return 0;
}
