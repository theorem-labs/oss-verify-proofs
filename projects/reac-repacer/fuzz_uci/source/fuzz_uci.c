// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>

/* fuzz_uci: the SIGHUP path's reading of the hot parameters, as the housekeeper
 * in tools/reac_repacer.c stages them. For each of the five, it runs
 * `uci -q get reac-repacer.main.<option>` and reads the reply with rp_uci_int
 * (src/repace_conf.c), keeping the running value for a reply that is no int; then
 * it holds the five to their ranges with rp_hot_clamp, which a ubus set goes
 * through too. The reply is what /etc/config/reac-repacer holds, which LuCI and
 * anyone with a shell on the router write.
 *
 * Input: one byte, whose bit 0 picks the ring the adaptive margin is held to (the
 * packaged builds' 2048 slots, or the source's 16384, less 64 each); then, for
 * prefill_ms, adapt_min_ms, adapt_max_ms, adapt_margin and servo_clamp_ppm in
 * turn, the running value (four bytes, little-endian), the reply's length (one
 * byte) and the reply. Bytes the input runs out of read as 0, and a reply cut by
 * the end of the input is the bytes left.
 *
 * Properties, each in a check_ function of its own, `if (cond) abort();`:
 *   no_overread  a reply's value is the one its own bytes give: the reply with "0"
 *                after it and with " " after it gives one value
 *   value        the value is the one the reply's grammar gives, read by the
 *                harness (include/repace_conf.h:38-42): the first line is optional
 *                blanks, an optional sign, decimal digits, optional blanks or a CR;
 *                its value when it fits an int, else the running value
 *   clamp        the staged parameters are those values held to the ranges, which
 *                are the harness's own (below), never the reader's
 */
#include <limits.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "fuzz.h"
#include "repace_conf.h"

/* The ranges. contract: include/repace_conf.h:23-35 (the ranges, and the ceiling
 * of adapt_margin the daemon passes in); tools/reac_repacer.c `#define RING_BITS`
 * (14 in the source, 11 in the packaged builds), and the 64 slots the pacer keeps
 * free. Defined here, so a reader whose range moves turns clamp red. */
#define PREFILL_MIN  1
#define PREFILL_MAX  1000
#define ADAPT_MIN    1
#define ADAPT_MAX    1000
#define SERVO_MAX    50000
static const int MARGIN_MAX[2] = { (1 << 11) - 64, (1 << 14) - 64 };

/* the value of a reply, by the grammar, or cur */
static int expected_value(const uint8_t *r, size_t n, int cur)
{
	size_t end = 0, i = 0;
	while (end < n && r[end] != '\n')
		end++;
	while (i < end && (r[i] == ' ' || r[i] == '\t'))
		i++;
	int neg = i < end && r[i] == '-';
	if (i < end && (r[i] == '-' || r[i] == '+'))
		i++;
	size_t d0 = i;
	long long v = 0;
	while (i < end && r[i] >= '0' && r[i] <= '9') {
		if (v < 10000000000LL)   /* past it, the value is past an int and stays so */
			v = v * 10 + (r[i] - '0');
		i++;
	}
	if (i == d0)
		return cur;
	while (i < end && (r[i] == ' ' || r[i] == '\t' || r[i] == '\r'))
		i++;
	if (i != end)
		return cur;
	if (neg)
		v = -v;
	return v < INT_MIN || v > INT_MAX ? cur : (int)v;
}

static int hold(int x, int lo, int hi)
{
	return x < lo ? lo : x > hi ? hi : x;
}

static __attribute__((noinline)) void check_no_overread(const uint8_t *r, size_t n, int cur)
{
	char *a = malloc(n + 1), *b = malloc(n + 1);

	/* not a property: the harness's own allocation failed */
	if (!a || !b)
		abort();
	if (n) {
		memcpy(a, r, n);
		memcpy(b, r, n);
	}
	a[n] = '0';
	b[n] = ' ';
	/* What follows the reply's last byte changes no value.
	 * contract: include/repace_conf.h:38 (the reply, n bytes)
	 * mutant: src/repace_conf.c:39 `*end = reply + n;` -> `*end = reply + n + 1;`
	 * input: prefill-15-unterminated */
	if (rp_uci_int(a, n, cur) != rp_uci_int(b, n, cur))
		abort();
	free(a);
	free(b);
}

static __attribute__((noinline)) int check_value(const uint8_t *r, size_t n, int cur)
{
	char *c = (char *)fuzz_dup(r, n);
	int got = rp_uci_int(c, n, cur);
	/* The value is the reply's, by its grammar, or the running one.
	 * contract: include/repace_conf.h:38-42
	 * mutant: src/repace_conf.c:43 `*p == ' ' || *p == '\t'` -> `*p == ' '`
	 * input: prefill-tab-150
	 * mutant: src/repace_conf.c:47 `neg = *p == '-';` -> `neg = 0;`
	 * input: servo-minus-20
	 * mutant: src/repace_conf.c:65 `v > INT_MAX` -> `v > (long long)INT_MAX + 1`
	 * input: prefill-2147483648
	 * mutant: src/repace_conf.c:55 `(long long)INT_MAX + 1` -> `1000`
	 * input: prefill-150000
	 * mutant: src/repace_conf.c:59 `*p == '\r'` -> `0`
	 * input: prefill-150-crlf
	 * mutant: src/repace_conf.c:59 `*p == ' ' || ` -> ``
	 * input: prefill-150-trailing-space
	 * mutant: src/repace_conf.c:41 `if (lf)` -> `if (0)`
	 * input: prefill-15-second-line
	 * mutant: src/repace_conf.c:61 `p != end` -> `p > end`
	 * input: prefill-15ms
	 * mutant: src/repace_conf.c:51 `return cur;` -> `return 0;`
	 * input: prefill-blank-line */
	if (got != expected_value(r, n, cur))
		abort();
	free(c);
	return got;
}

static __attribute__((noinline)) void check_clamp(const struct rp_hot *in, int margin_max)
{
	struct rp_hot p = *in;
	rp_hot_clamp(&p, margin_max);
	int amin = hold(in->adapt_min_ms, ADAPT_MIN, ADAPT_MAX);
	/* Each parameter is held to its range; the adaptive ceiling to the floor's
	 * value and above.
	 * contract: include/repace_conf.h:23-35
	 * mutant: include/repace_conf.h:28 `1000` -> `999`
	 * input: prefill-1000
	 * mutant: src/repace_conf.c:13 `p->prefill_ms < RP_PREFILL_MS_MIN` -> `p->prefill_ms < 0`
	 * input: prefill-0 */
	if (p.prefill_ms != hold(in->prefill_ms, PREFILL_MIN, PREFILL_MAX))
		abort();
	/* mutant: src/repace_conf.c:19 `p->adapt_min_ms > RP_ADAPT_MS_MAX` -> `0`
	 * input: adapt-min-2000
	 * mutant: include/repace_conf.h:29 `1` -> `2`
	 * input: adapt-min-1 */
	if (p.adapt_min_ms != amin)
		abort();
	/* mutant: src/repace_conf.c:23 `p->adapt_max_ms < p->adapt_min_ms` -> `0`
	 * input: adapt-max-below-min
	 * mutant: include/repace_conf.h:30 `1000` -> `1001`
	 * input: adapt-max-1001 */
	if (p.adapt_max_ms != hold(in->adapt_max_ms, amin, ADAPT_MAX))
		abort();
	/* mutant: src/repace_conf.c:27 `p->adapt_margin > margin_max` -> `p->adapt_margin > margin_max + 1`
	 * input: margin-past-ring-2048
	 * mutant: src/repace_conf.c:25 `p->adapt_margin < 0` -> `p->adapt_margin < -1`
	 * input: margin-minus-1 */
	if (p.adapt_margin != hold(in->adapt_margin, 0, margin_max))
		abort();
	/* mutant: include/repace_conf.h:31 `50000` -> `5000`
	 * input: servo-20000
	 * mutant: src/repace_conf.c:29 `p->servo_clamp_ppm < 0` -> `p->servo_clamp_ppm < -5`
	 * input: servo-minus-3 */
	if (p.servo_clamp_ppm != hold(in->servo_clamp_ppm, 0, SERVO_MAX))
		abort();
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	if (size >= FUZZ_INPUT_MAX)
		return 0;
	size_t at = size ? 1 : 0;
	int margin_max = MARGIN_MAX[size ? data[0] & 1 : 0];
	int v[5];
	for (int i = 0; i < 5; i++) {
		uint8_t cur[4] = { 0 }, len = 0;
		for (int b = 0; b < 4; b++)
			cur[b] = at < size ? data[at++] : 0;
		if (at < size)
			len = data[at++];
		size_t n = size - at < len ? size - at : len;
		check_no_overread(data + at, n, (int)fuzz_le32(cur));
		v[i] = check_value(data + at, n, (int)fuzz_le32(cur));
		at += n;
	}
	struct rp_hot p = { v[0], v[1], v[2], v[3], v[4] };
	check_clamp(&p, margin_max);
	return 0;
}
