// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>

/* fuzz_lock: rp_lock_lookup of src/repace_conf.c, the reader of the warm-start
 * lock (/etc/reac-repacer.lock, or --lockfile). lock_load in tools/reac_repacer.c
 * reads the file whole, up to one byte past RP_LOCK_MAX, and hands the bytes here,
 * once for each port, with the rate the daemon detected. The file is the daemon's
 * own, from an earlier run; a damaged or hand-edited one must restore no period
 * the grammar does not give.
 *
 * Input: one byte, the rate (its value modulo 5: 44100, 48000, 96000, and 88200 and
 * 0, which are no rate the daemon detects); one byte k, the port name's length
 * (k modulo 16); k bytes, the name; then the file. A name is an interface name,
 * 1 to 15 bytes with no NUL, space, tab, CR or LF; another is outside the
 * domain of the property, and the harness returns -1.
 *
 * Properties, each in a check_ function of its own, `if (cond) abort();`:
 *   no_overread  the answer is the one the file's own bytes give: the same file
 *                with "0" after it and with " " after it gives one answer
 *   lookup       the answer is the one the grammar below gives, read by the
 *                harness, never by the reader under test. The reader's limit of
 *                the file's size is the harness's own (LOCK_MAX)
 *
 * The grammar (include/repace_conf.h:45-60): lines end at LF; fields are
 * separated by spaces, tabs and CRs. A line holding a NUL byte is no record. A line
 * with no field, or whose first field starts with '#', is a comment. A record is a
 * line of three fields or more: the port name, the period and the rate label, each
 * of the last two 1 to 18 decimal digits. It restores its period when the name is
 * the port, the label is the rate, and the period is within 5% of the rate's
 * standard period, 12e9 / rate rounded to the nearest nanosecond, the 5% being
 * that period divided by 20 (integer division), bounds included. The last such
 * record wins. A file of more than LOCK_MAX bytes restores nothing, and so does a
 * rate the daemon never detects.
 */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "fuzz.h"
#include "repace_conf.h"

/* The largest lock the daemon reads. contract: include/repace_conf.h:61
 * (RP_LOCK_MAX, a text of more than it is no lock the daemon wrote); defined here,
 * so a reader whose limit moves turns lookup red */
#define LOCK_MAX 65536

static const long RATES[5] = { 44100, 48000, 96000, 88200, 0 };

static int is_sep(uint8_t c)
{
	return c == ' ' || c == '\t' || c == '\r';
}

/* the standard period of a rate the daemon detects: one 12-sample frame, in ns,
 * rounded to the nearest; 0 for any other rate */
static long standard(long rate)
{
	if (rate != 44100 && rate != 48000 && rate != 96000)
		return 0;
	return (long)((12000000000LL + rate / 2) / rate);
}

/* the value of a field of 1 to 18 decimal digits, -1 for any other field */
static long long number(const uint8_t *s, size_t len)
{
	long long v = 0;
	if (len < 1 || len > 18)
		return -1;
	for (size_t i = 0; i < len; i++) {
		if (s[i] < '0' || s[i] > '9')
			return -1;
		v = v * 10 + (s[i] - '0');
	}
	return v;
}

/* The period the grammar restores for the port at the rate, from the file. */
static long expected(const uint8_t *t, size_t n, const uint8_t *port, size_t k, long rate)
{
	long std = standard(rate), found = 0;
	if (n > LOCK_MAX || std == 0)
		return 0;
	size_t i = 0;
	while (i < n) {
		size_t end = i;
		while (end < n && t[end] != '\n')
			end++;
		/* the line's fields, the first three of them */
		const uint8_t *fs[3] = { 0 };
		size_t fl[3] = { 0 }, nf = 0;
		int nul = 0;
		for (size_t j = i; j < end; j++)
			nul |= t[j] == 0;
		for (size_t j = i; j < end && nf < 3;) {
			if (is_sep(t[j])) {
				j++;
				continue;
			}
			fs[nf] = t + j;
			while (j < end && !is_sep(t[j]))
				j++;
			fl[nf] = (size_t)(t + j - fs[nf]);
			nf++;
		}
		i = end + 1;
		if (nul || nf < 3 || fs[0][0] == '#')
			continue;
		if (fl[0] != k || memcmp(fs[0], port, k) != 0)
			continue;
		long long per = number(fs[1], fl[1]), lab = number(fs[2], fl[2]);
		if (per < 0 || lab != rate)
			continue;
		if (per < std - std / 20 || per > std + std / 20)
			continue;
		found = (long)per;
	}
	return found;
}

static __attribute__((noinline)) void check_no_overread(const uint8_t *t, size_t n, const char *port, long rate)
{
	char *a = malloc(n + 1), *b = malloc(n + 1);

	/* not a property: the harness's own allocation failed */
	if (!a || !b)
		abort();
	if (n) {
		memcpy(a, t, n);
		memcpy(b, t, n);
	}
	a[n] = '0';
	b[n] = ' ';
	/* What follows the file's last byte changes no answer.
	 * contract: include/repace_conf.h:45 (the file's n bytes)
	 * mutant: src/repace_conf.c:121 `*stop = text + n;` -> `*stop = text + n + 1;`
	 * input: last-label-unterminated */
	if (rp_lock_lookup(a, n, port, rate) != rp_lock_lookup(b, n, port, rate))
		abort();
	free(a);
	free(b);
}

static __attribute__((noinline)) void check_lookup(const uint8_t *t, size_t n, const char *port, size_t k, long rate)
{
	char *c = (char *)fuzz_dup(t, n);
	long got = rp_lock_lookup(c, n, port, rate);
	long want = expected(t, n, (const uint8_t *)port, k, rate);
	/* The period restored is the grammar's.
	 * contract: include/repace_conf.h:45-60 (the record grammar and the 5% band)
	 * mutant: src/repace_conf.c:74 `case 44100: return 272109;` -> `case 44100: return 272108;`
	 * input: rate-44100-upper-edge
	 * mutant: src/repace_conf.c:75 `return 250000;` -> `return 250001;`
	 * input: rate-48000-lower-edge
	 * mutant: src/repace_conf.c:140 `per < std - std / 20` -> `per <= std - std / 20`
	 * input: rate-96000-lower-edge
	 * mutant: src/repace_conf.c:140 `per > std + std / 20` -> `per >= std + std / 20`
	 * input: rate-96000-upper-edge
	 * mutant: src/repace_conf.c:138 `lab != rate_hz` -> `lab < rate_hz`
	 * input: label-192000
	 * mutant: src/repace_conf.c:135 `name_len != plen || ` -> ``
	 * input: port-prefix-lan10
	 * mutant: src/repace_conf.c:133 `name_len == 0 || name[0] == '#'` -> `name_len == 0`
	 * input: port-hash-comment
	 * mutant: src/repace_conf.c:131 `if (has_nul)` -> `if (0)`
	 * input: nul-in-fourth-field
	 * mutant: src/repace_conf.c:103 `len > 18` -> `len > 19`
	 * input: period-19-digits
	 * mutant: src/repace_conf.c:107 `s[i] < '0' || s[i] > '9'` -> `s[i] < '0'`
	 * input: period-colon
	 * mutant: src/repace_conf.c:83 `c == '\r'` -> `0`
	 * input: crlf-lines
	 * mutant: src/repace_conf.c:142 `found = (long)per;` -> `if (!found) found = (long)per;`
	 * input: two-records-last-wins
	 * mutant: include/repace_conf.h:61 `65536` -> `65537`
	 * input: lock-past-max */
	if (got != want)
		abort();
	free(c);
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	/* an input too short to hold the rate, the name's length and the name holds no
	 * file to read */
	if (size < 2 || size >= FUZZ_INPUT_MAX)
		return 0;
	long rate = RATES[data[0] % 5];
	size_t k = data[1] % 16;
	if (size < 2 + k)
		return 0;
	if (k == 0)
		return -1;
	char port[16];
	for (size_t i = 0; i < k; i++) {
		uint8_t c = data[2 + i];
		if (c == 0 || c == '\n' || is_sep(c))
			return -1;
		port[i] = (char)c;
	}
	port[k] = '\0';
	const uint8_t *t = data + 2 + k;
	size_t n = size - 2 - k;

	check_no_overread(t, n, port, rate);
	check_lookup(t, n, port, k, rate);
	return 0;
}
