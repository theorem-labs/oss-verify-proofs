// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>

/* fuzz_egress: every write of src/repace_wire.c into a frame the daemon emits.
 * The pacer (pace_one and ds_emit_one in tools/reac_repacer.c) takes a frame the
 * forward reader queued, or the last one again as gap concealment, and before it
 * sends it: stamps its own output counter on it (rp_restamp); during a rate change,
 * mutes it (rp_mute); and with --inject-sine or --inject-copy, asks whether the
 * frame holds the injected slot (rp_slot_width) and writes 12 samples into it
 * (rp_slot_write). The frame is bytes from the wire; so is the copy source's
 * slot of the samples inject-copy writes.
 *
 * Input: one byte, the slot less 2 (-2..253); four bytes, the output counter,
 * little-endian; twelve times four bytes, the samples, little-endian; then the
 * frame, of which the pacer holds at most the first 1600 bytes (the ring's slot,
 * as large as the receive buffer). Bytes missing from the first 53 read as 0.
 *
 * Properties, each in a check_ function of its own, `if (cond) abort();`. The
 * expected frame is the harness's own, from the frame as fuzz/fuzz.h lays it out:
 *   restamp  the frame carries the counter's low 16 bits at bytes 14-15,
 *            little-endian, and every other byte as it was
 *   mute     an audio frame of more than 18 bytes is zero from byte 18 to its end,
 *            with bytes 0-17 as they were; any other frame is as it was
 *   gate     a frame holds the slot when it is an audio frame whose width, by the
 *            frame law, holds it; the gate answers that width, or -1
 *   inject   a frame that holds the slot carries the low 24 bits of each sample at
 *            the braid's three bytes for that slot and time-sample, and every other
 *            byte as it was; a frame that does not is as it was
 */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "fuzz.h"
#include "repace_wire.h"

#define HEAD 53   /* slot byte, counter, 12 samples */

static __attribute__((noinline)) void check_restamp(const uint8_t *f, size_t n, uint32_t ctr)
{
	/* The pacer restamps a frame of its ring or its concealment buffer, so one the
	 * forward reader queued: 18 bytes or more. A shorter one never reaches it. */
	if (n < 18)
		return;
	uint8_t *c = fuzz_dup(f, n);
	rp_restamp(c, ctr);
	/* Bytes 14-15 carry the counter's low 16 bits, little-endian.
	 * contract: include/repace_wire.h:11 (the counter, little-endian), :74-75
	 * mutant: src/repace_wire.c:144 `ctr & 0xff` -> `ctr >> 8 & 0xff`
	 * input: s0808-audio-ctr-1234
	 * mutant: src/repace_wire.c:145 `(ctr >> 8) & 0xff` -> `(ctr >> 9) & 0xff`
	 * input: s0808-audio-ctr-1234 */
	if (c[14] != (uint8_t)ctr || c[15] != (uint8_t)(ctr >> 8))
		abort();
	/* Every other byte is as it was.
	 * mutant: src/repace_wire.c:145 `f[15]` -> `f[16]`
	 * input: s0808-audio-ctr-1234 */
	if (memcmp(c, f, 14) != 0 || memcmp(c + 16, f + 16, n - 16) != 0)
		abort();
	free(c);
}

static __attribute__((noinline)) void check_mute(const uint8_t *f, size_t n)
{
	uint8_t *c = fuzz_dup(f, n);
	rp_mute(c, n);
	int muted = n > 18 && w_is_audio(f);
	size_t keep = muted ? 18 : n;
	/* The bytes the mute keeps: the first 18 of an audio frame, all of any other.
	 * contract: include/repace_wire.h:78-79
	 * mutant: src/repace_wire.c:150 `n > 18 && is_audio(f)` -> `n > 18`
	 * input: s1608-ctrl-cdea
	 * mutant: src/repace_wire.c:151 `memset(f + 18, 0, n - 18)` -> `memset(f + 14, 0, n - 14)`
	 * input: s0808-audio-ctr-1234 */
	if (memcmp(c, f, keep) != 0)
		abort();
	for (size_t i = keep; i < n; i++) {
		/* An audio frame is zero from byte 18 to its end.
		 * mutant: src/repace_wire.c:150 `n > 18` -> `n > 50`
		 * input: audio-19
		 * mutant: src/repace_wire.c:151 `n - 18` -> `n - 20`
		 * input: s0808-audio-ctr-1234 */
		if (c[i] != 0)
			abort();
	}
	free(c);
}

static int want_width(const uint8_t *f, size_t n, int slot)
{
	int nch = w_width((long)n);   /* -1 below 124 bytes, so the type bytes are there */
	if (nch < 0 || !w_is_audio(f) || slot < 0 || slot >= nch)
		return -1;
	return nch;
}

static __attribute__((noinline)) void check_gate(const uint8_t *f, size_t n, int slot)
{
	/* The injectors write only into an audio frame whose width holds the slot.
	 * contract: include/repace_wire.h:61-63
	 * mutant: src/repace_wire.c:103 `n < 50 || !is_audio(f)` -> `n < 50`
	 * input: s1608-ctrl-cdea-slot-0
	 * mutant: src/repace_wire.c:106 `slot >= nch` -> `slot >= nch + 2`
	 * input: s0808-audio-slot-9 */
	if (rp_slot_width(f, n, slot) != want_width(f, n, slot))
		abort();
}

static __attribute__((noinline)) void check_inject(const uint8_t *f, size_t n, int slot, const int32_t v[12])
{
	uint8_t *c = fuzz_dup(f, n), *e = fuzz_dup(f, n);
	int nch = want_width(f, n, slot);
	if (nch > 0)
		for (int s = 0; s < W_SAMPLES; s++)
			w_put(e, s, slot, nch, v[s]);
	int got = rp_slot_write(c, n, slot, v);
	/* The writer writes exactly when the gate lets it.
	 * contract: include/repace_wire.h:70-71
	 * mutant: src/repace_wire.c:139 `return 1;` -> `return nch > 2;`
	 * input: s2-audio-slot-0 */
	if (got != (nch > 0))
		abort();
	/* The frame is the one the braid gives: each sample's low 24 bits at its three
	 * bytes, and every other byte as it was.
	 * contract: <reac/reac_braid.h> (the pair packed big-endian s24, each 16-bit
	 * word byte-swapped), fuzz/fuzz.h w_put
	 * mutant: src/repace_wire.c:137 `(v[s] >> 16) & 0xff` -> `(v[s] >> 15) & 0xff`
	 * input: s0808-audio-slot-3
	 * mutant: src/repace_wire.c:136 `a[pos[1]]` -> `a[pos[0]]`
	 * input: s0808-audio-slot-3
	 * mutant: src/repace_wire.c:134 `reac_braid_pos(s, slot, nch, pos);` -> `reac_braid_pos(s, slot, nch - 2, pos);`
	 * input: s1608-audio-residue-slot-15
	 * mutant: src/repace_wire.c:132 `s < REAC_SAMPLES_PER_PKT` -> `s < REAC_SAMPLES_PER_PKT - 1`
	 * input: s0808-audio-slot-3
	 * mutant: src/repace_wire.c:131 `f + REAC_AUDIO_OFFSET` -> `f + REAC_AUDIO_OFFSET + 2`
	 * input: s40-downstream-slot-39 */
	if (memcmp(c, e, n) != 0)
		abort();
	free(c);
	free(e);
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	if (size >= FUZZ_INPUT_MAX)
		return 0;
	uint8_t head[HEAD] = { 0 };
	memcpy(head, data, size < HEAD ? size : HEAD);
	int slot = (int)head[0] - 2;
	uint32_t ctr = fuzz_le32(head + 1);
	int32_t v[W_SAMPLES];
	for (int s = 0; s < W_SAMPLES; s++)
		v[s] = (int32_t)fuzz_le32(head + 5 + 4 * s);
	size_t n = size > HEAD ? size - HEAD : 0;
	if (n > W_RECV_MAX)
		n = W_RECV_MAX;
	uint8_t *f = fuzz_dup(data + HEAD * (size > HEAD), n);

	check_restamp(f, n, ctr);
	check_mute(f, n);
	check_gate(f, n, slot);
	check_inject(f, n, slot, v);
	free(f);
	return 0;
}
