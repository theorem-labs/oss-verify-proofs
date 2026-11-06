// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>

/* fuzz_wire: every reader of src/repace_wire.c that takes a frame off the wire,
 * on one frame. The daemon reads a frame in five places (tools/reac_repacer.c):
 * the forward reader (rp_fwd_class), the return relay (rp_ret_accept), the
 * downstream listener (rp_ds_accept), the clock meter (rp_meter_counter) and the
 * inject-copy reader (rp_copy_untag, rp_slot_read on each frame and the one it keeps);
 * and the pacer seeds its output counter from a queued frame (rp_counter). The
 * width rule they share, rp_frame_channels, is checked on the frame's length.
 *
 * Input: one byte, then the frame. The byte's bit 0 is --bcast-only; the rest of
 * it, less 2, is the channel slot the copy reader reads (-2..125, so a slot below
 * 0 and past every width are both inputs). The frame reaches each reader as at
 * most its first 1600 bytes, as recvfrom into the daemon's buffer hands it over.
 *
 * Properties, each in a check_ function of its own, `if (cond) abort();`. The
 * expected answer is the harness's own, from the frame as fuzz/fuzz.h lays it
 * out, never from the reader:
 *   forward     a frame is queued as audio or as control, or dropped, as the
 *               forward reader's rule says (include/repace_wire.h:26-29)
 *   ret         the return relay passes exactly the REAC frames of 14 bytes or more
 *   downstream  the listener stamps exactly the REAC frames of 18 bytes or more,
 *               untagged or VLAN-tagged
 *   meter       the meter counts exactly the REAC frames of 1000 bytes or more,
 *               untagged or tagged, and reads the counter two bytes after the
 *               EtherType, little-endian; a frame it skips leaves the counter
 *   counter     a queued frame's counter is bytes 14-15, little-endian
 *   width       the width of a length is the frame law's, and no negative length
 *               has one
 *   copy        the copy reader keeps exactly the REAC audio frames of 50 bytes or
 *               more, a tagged one with its four tag bytes removed and nothing
 *               else moved
 *   read        the 12 samples of a slot are the ones the braid puts there, read
 *               only when the frame's width holds the slot; a declined read leaves
 *               the samples (rp_slot_read takes the frame const, so a read
 *               writes no byte of it)
 */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "fuzz.h"
#include "repace_wire.h"

/* a value no reader writes: a counter or sample a declined call left alone */
#define UNTOUCHED_CTR    0xa5c3u
#define UNTOUCHED_SAMPLE 0x5a5a5a5a

static __attribute__((noinline)) void check_forward(const uint8_t *f, size_t n, int bcast)
{
	int got = rp_fwd_class(f, n, bcast);
	int want = RP_FWD_DROP;
	if (n >= 18 && w_is_reac(f, 12) && (!bcast || f[0] == 0xff))
		want = w_is_audio(f) ? RP_FWD_AUDIO : RP_FWD_CTRL;
	/* The forward reader queues a REAC frame of 18 bytes or more, with
	 * --bcast-only only one to a destination starting 0xff, as audio when its
	 * type is 00 00 and as control otherwise; it drops every other frame.
	 * contract: include/repace_wire.h:26-29 (the forward reader's rule)
	 * mutant: src/repace_wire.c:36 `n < 18` -> `n < 14`
	 * input: reac-ctrl-17
	 * mutant: src/repace_wire.c:40 `bcast_only && f[0] != 0xff` -> `bcast_only && f[1] != 0xff`
	 * input: bcast-only-unicast-first-byte
	 * mutant: src/repace_wire.c:42 `is_audio(f) ? RP_FWD_AUDIO : RP_FWD_CTRL` -> `RP_FWD_AUDIO`
	 * input: s1608-ctrl-cdea
	 * mutant: src/repace_wire.c:31 `f[16] == 0x00 && f[17] == 0x00` -> `f[16] == 0x00`
	 * input: s1608-ctrl-00ea */
	if (got != want)
		abort();
}

static __attribute__((noinline)) void check_ret(const uint8_t *f, size_t n)
{
	int want = n >= 14 && w_is_reac(f, 12);
	/* The return relay passes every REAC frame of 14 bytes or more, handshakes
	 * included, and nothing else.
	 * contract: include/repace_wire.h:33-34
	 * mutant: src/repace_wire.c:47 `n >= 14 && is_reac(f)` -> `n >= 14`
	 * input: not-reac-ipv4
	 * mutant: src/repace_wire.c:47 `n >= 14` -> `n >= 18`
	 * input: reac-handshake-14 */
	if (rp_ret_accept(f, n) != want)
		abort();
}

static __attribute__((noinline)) void check_downstream(const uint8_t *f, size_t n)
{
	int want = n >= 18 && (w_is_reac(f, 12) || (w_is_tag(f) && w_is_reac(f, 16)));
	/* The downstream listener stamps every REAC frame of 18 bytes or more, untagged
	 * or behind one 802.1Q tag, and nothing else.
	 * contract: include/repace_wire.h:37-38
	 * mutant: src/repace_wire.c:54 `is_reac(f) || is_tagged_reac(f)` -> `is_reac(f)`
	 * input: s0808-audio-tagged
	 * mutant: src/repace_wire.c:25 `f[16] == 0x88 && f[17] == 0x19` -> `f[16] == 0x88`
	 * input: tagged-not-reac */
	if (rp_ds_accept(f, n) != want)
		abort();
}

static __attribute__((noinline)) void check_meter(const uint8_t *f, size_t n)
{
	size_t eo = (n > 13 && w_is_tag(f)) ? 16 : 12;
	int want = n >= 1000 && n >= eo + 6 && w_is_reac(f, eo);
	uint16_t ctr = UNTOUCHED_CTR;
	int got = rp_meter_counter(f, n, &ctr);
	/* The meter counts every REAC frame of 1000 bytes or more, untagged or tagged,
	 * and no other: a shorter frame is a control frame or a handshake, whose counter
	 * the clock must not sum.
	 * contract: include/repace_wire.h:41-43
	 * mutant: src/repace_wire.c:61 `n < 1000` -> `n < 100`
	 * input: s0808-audio
	 * mutant: src/repace_wire.c:59 `? 16 : 12` -> `? 12 : 12`
	 * input: s4000-audio-tagged
	 * mutant: src/repace_wire.c:61 `n < 1000` -> `n <= 1000`
	 * input: reac-1000
	 * mutant: src/repace_wire.c:59 `f[13] == 0x00` -> `1`
	 * input: s4000-tag-81-01 */
	if (got != want)
		abort();
	/* The counter is the two bytes after the EtherType, little-endian.
	 * contract: include/repace_wire.h:11 (bytes 14-15, the counter, little-endian)
	 * mutant: src/repace_wire.c:65 `f[eo + 2] | (f[eo + 3] << 8)` -> `f[eo + 3] | (f[eo + 2] << 8)`
	 * input: s4000-audio */
	if (want && ctr != (uint16_t)(f[eo + 2] | f[eo + 3] << 8))
		abort();
	/* A frame the meter skips leaves the counter as it was.
	 * mutant: src/repace_wire.c:64 `return 0;` -> `return (*ctr = 0);`
	 * input: s4000-audio-not-reac */
	if (!want && ctr != UNTOUCHED_CTR)
		abort();
}

static __attribute__((noinline)) void check_counter(const uint8_t *f, size_t n)
{
	/* The pacer seeds its output counter from a frame the forward reader queued,
	 * so only from a frame of 18 bytes or more; a shorter one never reaches it. */
	if (n < 18)
		return;
	/* contract: include/repace_wire.h:11 (bytes 14-15, little-endian)
	 * mutant: src/repace_wire.c:71 `f[14] | (f[15] << 8)` -> `f[15] | (f[14] << 8)`
	 * input: s0808-audio */
	if (rp_counter(f) != (unsigned)(f[14] | f[15] << 8))
		abort();
}

static __attribute__((noinline)) void check_width(size_t n)
{
	/* The width of a length is the frame law's: 52 + nch * 36 bytes for an even
	 * nch of 2..40, or two bytes more with the FCS residue.
	 * contract: include/repace_wire.h:50-52
	 * mutant: src/repace_wire.c:83 `nch > REAC_MAX_CHANNELS` -> `nch > 32`
	 * input: downstream-40ch
	 * mutant: src/repace_wire.c:83 `(nch & 1)` -> `0`
	 * input: odd-width-3ch
	 * mutant: src/repace_wire.c:78 `reac_frame_clean_len((size_t)len)` -> `(size_t)len`
	 * input: s1608-audio-residue
	 * mutant: src/repace_wire.c:83 `nch > REAC_MAX_CHANNELS` -> `nch > 42`
	 * input: past-40ch-42ch-1564
	 * mutant: src/repace_wire.c:83 `nch < 2` -> `nch < 0`
	 * input: reac-52 */
	if (rp_frame_channels((long)n) != w_width((long)n))
		abort();
	/* No negative length has a width.
	 * mutant: src/repace_wire.c:77 `return -1;` -> `return 0;`
	 * input: empty-frame */
	if (rp_frame_channels(-1 - (long)n) != -1)
		abort();
}

/* The frame the copy reader keeps: a tagged REAC frame without its four tag
 * bytes, any other as it came; *len its length. */
static uint8_t *untagged(const uint8_t *f, size_t n, size_t *len)
{
	uint8_t *u = fuzz_dup(f, n);
	if (n >= 18 && w_is_tag(f) && w_is_reac(f, 16)) {
		memcpy(u + 12, f + 16, n - 16);
		*len = n - 4;
	} else {
		*len = n;
	}
	return u;
}

static __attribute__((noinline)) size_t check_copy(uint8_t *c, const uint8_t *f, size_t n)
{
	size_t ulen, got = rp_copy_untag(c, n);
	uint8_t *u = untagged(f, n, &ulen);
	size_t want = (n >= 50 && w_is_reac(u, 12) && w_is_audio(u)) ? ulen : 0;
	/* The copy reader keeps every REAC audio frame of 50 bytes or more, untagged
	 * or tagged, and no other; a tagged one is 4 bytes shorter once kept.
	 * contract: include/repace_wire.h:55-58
	 * mutant: src/repace_wire.c:90 `n < 50` -> `n < 18`
	 * input: s0808-audio-short-49
	 * mutant: src/repace_wire.c:90 `n < 50` -> `n < 51`
	 * input: reac-audio-50
	 * mutant: src/repace_wire.c:96 `!reac_frame_is_reac(f, n) || !is_audio(f)` -> `!reac_frame_is_reac(f, n)`
	 * input: s1608-ctrl-cdea
	 * mutant: src/repace_wire.c:94 `n -= 4;` -> `n -= 0;`
	 * input: s0808-audio-tagged */
	if (got != want)
		abort();
	/* What it keeps is the frame with the tag bytes removed and nothing else moved;
	 * the daemon reads nothing of a frame the reader does not keep.
	 * mutant: src/repace_wire.c:93 `memmove(f + 12, f + 16, n - 16);` -> `memmove(f + 12, f + 16, n - 18);`
	 * input: s0808-audio-tagged */
	if (got && memcmp(c, u, got) != 0)
		abort();
	free(u);
	return got;
}

static __attribute__((noinline)) void check_read(const uint8_t *c, size_t len, int slot)
{
	int32_t v[W_SAMPLES];
	for (int s = 0; s < W_SAMPLES; s++)
		v[s] = UNTOUCHED_SAMPLE;
	int nch = w_width((long)len);
	int want = len >= 50 && w_is_audio(c) && nch > 0 && slot >= 0 && slot < nch;
	int got = rp_slot_read(c, len, slot, v);
	/* A slot is read only when the frame is audio and its width holds the slot.
	 * contract: include/repace_wire.h:61-67
	 * mutant: src/repace_wire.c:106 `slot >= nch` -> `slot > nch`
	 * input: s0808-audio-slot-8
	 * mutant: src/repace_wire.c:106 `slot < 0 || ` -> ``
	 * input: s0808-audio-slot-minus-1
	 * mutant: src/repace_wire.c:113 `rp_slot_width(f, n, slot)` -> `(slot >= 0 && slot < rp_frame_channels((long)n)) ? rp_frame_channels((long)n) : -1`
	 * input: s1608-ctrl-cdea */
	if (got != want)
		abort();
	for (int s = 0; s < W_SAMPLES; s++) {
		/* The samples are those the braid puts in that slot, sign-extended from
		 * 24 bits.
		 * contract: <reac/reac_braid.h> (the pair packed big-endian s24, each 16-bit
		 * word byte-swapped), fuzz/fuzz.h w_get
		 * mutant: src/repace_wire.c:121 `(x & 0x800000) ? x - (1 << 24) : x` -> `x`
		 * input: s0808-audio-slot-1
		 * mutant: src/repace_wire.c:120 `a[pos[0]] | (a[pos[1]] << 8)` -> `a[pos[1]] | (a[pos[0]] << 8)`
		 * input: s0808-audio-slot-0
		 * mutant: src/repace_wire.c:119 `reac_braid_pos(s, slot, nch, pos);` -> `reac_braid_pos(s, slot ^ 1, nch, pos);`
		 * input: s0808-audio-slot-0
		 * mutant: src/repace_wire.c:116 `f + REAC_AUDIO_OFFSET` -> `f + REAC_AUDIO_OFFSET - 2`
		 * input: s1608-audio-residue */
		if (got && v[s] != w_get(c, s, slot, nch))
			abort();
		/* A declined read leaves the samples as they were.
		 * mutant: src/repace_wire.c:115 `return 0;` -> `return v[0] = 0;`
		 * input: s0808-audio-slot-8 */
		if (!got && v[s] != UNTOUCHED_SAMPLE)
			abort();
	}
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	/* the empty input holds no flag byte; a frame of no bytes is the input of one */
	if (size < 1 || size >= FUZZ_INPUT_MAX)
		return 0;
	int bcast = data[0] & 1;
	int slot = (data[0] >> 1) - 2;
	size_t n = size - 1;
	if (n > W_RECV_MAX)
		n = W_RECV_MAX;
	uint8_t *f = fuzz_dup(data + 1, n);

	check_forward(f, n, bcast);
	check_ret(f, n);
	check_downstream(f, n);
	check_meter(f, n);
	check_counter(f, n);
	check_width(n);
	/* the reader's own rule, on every frame as it came, control frames included */
	check_read(f, n, slot);

	uint8_t *c = fuzz_dup(f, n);
	size_t len = check_copy(c, f, n);
	/* inj_copy_rx reads a slot of a frame the copy reader kept */
	if (len)
		check_read(c, len, slot);
	free(c);
	free(f);
	return 0;
}
