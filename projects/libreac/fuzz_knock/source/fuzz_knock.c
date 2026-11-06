// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>
// Modified by Theorem Labs, 2026-10-25: a modified copy of fuzz/fuzz_knock.c at libreac 9ed322ef.

/* libFuzzer harness: THE KNOCK (src/reac_knock.c), the proof that a wire carries no
 * master and may therefore be driven.
 *
 * Its only input from the wire is WHEN a frame was heard. The harness feeds it a
 * clock and a pattern of frames chosen by the input and checks the safety argument
 * reac_knock.h makes: a master fills every audio slot, so the licence to drive may
 * be granted only after REAC_KNOCK_LISTEN_NS in which nothing at all was heard.
 *
 * Input:  [0..3] u32 LE: the start time in units of 2^31 ns, so the start goes from
 *         0 to about 2^63 ns. The clock of a run thus stays below 2^64 - 1 -
 *         REAC_KNOCK_LISTEN_NS, and the library's sums `now + REAC_KNOCK_LISTEN_NS`
 *         cannot wrap.
 *         then events, at most 4096, each [ev][u16 LE dt]: the clock advances by
 *         dt << (ev >> 4 & 7) ns (one step runs from 1 ns to 65535 << 7 ns, about
 *         8.4 ms, so a 500 ms window takes some 60 steps or more), then
 *           ev & 1   a frame is heard (reac_knock_heard)
 *           ev & 2   the caller steps the knock (reac_knock_step)
 *         The clock is monotonic, like the CLOCK_MONOTONIC the daemon passes in.
 *
 * Properties, each an abort():
 *   - init starts a knock that listens, has no licence, and opened at the start;
 *   - step returns NONE or DRIVE;
 *   - DRIVE comes at most once in a knock's life, and `granted` is set exactly
 *     when DRIVE has come (a heard frame does not revoke it);
 *   - DRIVE comes only at a time at least REAC_KNOCK_LISTEN_NS after the wire came
 *     up AND after the last frame heard on it;
 *   - and it is not withheld: a step at or after that time, with nothing heard
 *     since and no licence yet granted, drives;
 *   - the state is PROVEN once DRIVE has come, else CANCELLED once a frame was
 *     heard, else LISTENING.
 *
 * Each property's comment records a mutant (a one-line change that makes the
 * library wrong on purpose) and a seed of fuzz_knock_seed_corpus.zip on which the
 * property stops it.
 */
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

#include <reac/reac_knock.h>

#include "fuzz.h"

#define MAX_EVENTS 4096

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	if (size >= FUZZ_INPUT_MAX)
		return 0;
	struct fuzz_in in = fuzz_in(data, size);
	uint64_t now = (uint64_t)fuzz_u32(&in) << 31;
	struct reac_knock k;
	reac_knock_init(&k, now);

	/* contract: include/reac/reac_knock.h:108 (init begins listening), :88, :102, :105
	 * mutant: src/reac_knock.c:13 `REAC_KNOCK_LISTENING` -> `REAC_KNOCK_CANCELLED`
	 * input: silent-wire
	 * mutant: src/reac_knock.c:18 `k->due_ns = now_ns + REAC_KNOCK_LISTEN_NS;` -> `k->due_ns = now_ns + REAC_KNOCK_LISTEN_NS; k->granted = 1;`
	 * input: silent-wire
	 * mutant: src/reac_knock.c:14 `k->opened_ns = now_ns;` -> `k->opened_ns = 0;`
	 * input: silent-wire
	 */
	if (k.state != REAC_KNOCK_LISTENING || k.granted != 0 || k.opened_ns != now)
		abort();

	/* The harness's own record of the wire: when it came up or was last heard
	 * (the clock never goes back, so this is never after now), whether a frame was
	 * ever heard, and how many DRIVEs step returned. */
	uint64_t quiet_since = now;
	int heard = 0;
	int drives = 0;

	for (int i = 0; i < MAX_EVENTS && in.n; i++) {
		uint8_t ev = fuzz_u8(&in);
		now += (uint64_t)fuzz_u16(&in) << (ev >> 4 & 7);
		if (ev & 1) {
			reac_knock_heard(&k, now);
			quiet_since = now;
			heard = 1;
		}
		if (ev & 2) {
			enum reac_knock_act a = reac_knock_step(&k, now);
			/* contract: include/reac/reac_knock.h:95-98
			 * mutant: src/reac_knock.c:55 `return REAC_KNOCK_ACT_DRIVE;` -> `return 2;`
			 * input: silent-wire
			 */
			if (a != REAC_KNOCK_ACT_NONE && a != REAC_KNOCK_ACT_DRIVE)
				abort();
			if (a == REAC_KNOCK_ACT_DRIVE) {
				drives++;
				/* Once, and with the licence set.
				 * contract: include/reac/reac_knock.h:93-94, :105, :121
				 * mutant: src/reac_knock.c:47 `k->state != REAC_KNOCK_LISTENING` -> `k->state == REAC_KNOCK_CANCELLED`
				 * input: silent-wire
				 * mutant: src/reac_knock.c:54 `k->granted = 1;` -> ``
				 * input: silent-wire
				 */
				if (drives > 1 || !k.granted)
					abort();
				/* Only after a whole window of silence. The first record is the
				 * sabotage patch fuzz/sabotage/knock.patch.
				 * contract: include/reac/reac_knock.h:34-37, :56-59, :85, :121-123
				 * mutant: src/reac_knock.c:49 `k->due_ns` -> `k->opened_ns`
				 * input: silent-wire
				 * mutant: src/reac_knock.c:28 `k->state == REAC_KNOCK_LISTENING` -> `0`
				 * input: frame-at-due
				 */
				if (now - quiet_since < REAC_KNOCK_LISTEN_NS)
					abort();
			}
			/* A silent window closed and no licence was granted: the licence is
			 * due, and withholding it is the latch the re-opening cancellation
			 * exists to prevent. (A frame heard this instant sets quiet_since to
			 * now, so the window is then open.)
			 * contract: include/reac/reac_knock.h:121-123 (on the first step at or
			 * after the observation closes)
			 * mutant: src/reac_knock.c:49 `now_ns < k->due_ns` -> `now_ns <= k->due_ns`
			 * input: exact-window
			 * mutant: src/reac_knock.c:42 `< REAC_KNOCK_LISTEN_NS` -> `<= REAC_KNOCK_LISTEN_NS`
			 * input: exact-reopen
			 * mutant: src/reac_knock.c:49 `now_ns < k->due_ns` -> `now_ns < k->due_ns || now_ns >> 53`
			 * input: late-start
			 */
			if (a == REAC_KNOCK_ACT_NONE && !drives && now - quiet_since >= REAC_KNOCK_LISTEN_NS)
				abort();
		}
		/* The licence is set exactly when the caller was told DRIVE, and a frame
		 * heard after it does not revoke it (reac_knock.h).
		 * contract: include/reac/reac_knock.h:105, :113-115
		 * mutant: src/reac_knock.c:23 `k->heard_ns = now_ns;` -> `k->heard_ns = now_ns; k->granted = 0;`
		 * input: stray-frame
		 * mutant: src/reac_knock.c:29 `k->state = REAC_KNOCK_CANCELLED;` -> `k->state = REAC_KNOCK_CANCELLED; k->granted = 1;`
		 * input: desk-talking
		 */
		if (k.granted != (drives != 0))
			abort();
		/* The state, from reac_knock.h: PROVEN after the DRIVE (a later frame
		 * does not change it); else CANCELLED after a frame. A cancelled knock
		 * re-opens only in a step at least a window after the frame, and that
		 * same step drives, so LISTENING is seen only before the first frame.
		 * contract: include/reac/reac_knock.h:88-90, :56, :118
		 * mutant: src/reac_knock.c:29 `k->state = REAC_KNOCK_CANCELLED;` -> `k->due_ns = now_ns + REAC_KNOCK_LISTEN_NS;`
		 * input: desk-talking
		 * mutant: src/reac_knock.c:53 `k->state = REAC_KNOCK_PROVEN;` -> ``
		 * input: silent-wire
		 * mutant: src/reac_knock.c:28 `k->state == REAC_KNOCK_LISTENING` -> `k->state != REAC_KNOCK_CANCELLED`
		 * input: stray-frame
		 */
		if (k.state != (drives ? REAC_KNOCK_PROVEN : heard ? REAC_KNOCK_CANCELLED : REAC_KNOCK_LISTENING))
			abort();
	}
	return 0;
}
