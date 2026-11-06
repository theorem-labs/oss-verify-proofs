// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>
// Modified by Theorem Labs, 2026-10-25: a modified copy of fuzz/fuzz_decode.c at libreac 9ed322ef.

/* libFuzzer harness: the AUDIO FRAME decoders (src/reac_decode.c,
 * src/reac_upstream.c, and the frame helpers in src/reac.c).
 *
 * Input:  [0] mode selector  [1] n_channels  [2] samples_per_pkt  [3..] the frame
 *
 * The selector's low two bits pick REAC_MODE_44K1 / _48K / _96K, or (3) a
 * descriptor built from bytes 1 and 2 read as signed: the geometry guard in
 * reac_decode() exists for a caller's descriptor, so the harness has to be able to
 * hand it a bad one. The frame is everything after the header, at its own length,
 * in its own allocation (fuzz_dup(): malloc(0) for an empty frame, which can be
 * NULL; every reader then sees length 0 and reads no byte).
 *
 * Properties, each an abort():
 *   - reac_frame_inspect() calls a frame valid exactly when it has 1492 bytes,
 *     EtherType 88 19 and the end marker C2 EA, and its counter is bytes 14-15
 *     little-endian;
 *   - the decoders agree with reac_frame_inspect(): a frame decodes exactly when
 *     inspect calls it valid and the geometry fits (and, for reac_decode(), the
 *     width is even), and then returns its ns;
 *   - a decoder that refuses a frame (returns -1) writes nothing into its output
 *     (reac_decode.h, reac_upstream.h: on -1, out is untouched);
 *   - the braid is a bijection: decoding then re-encoding through
 *     reac_braid_encode() gives back the audio region byte for byte, downstream
 *     and upstream (for a geometry of 12 samples or fewer, where the encoder
 *     works);
 *   - every decoded sample, downstream and upstream, is the three bytes the braid
 *     map of reac_braid.h puts it in, the map written out in the harness;
 *   - reac_decode_plain_le() is a straight copy: each sample (ch, s) is the 3
 *     bytes at (s * n_channels + ch) * 3;
 *   - reac_upstream_channels() is the frame's geometry (52 + 36 per channel,
 *     worked out in the harness) restricted to box widths, the even widths
 *     REAC_BOX_MIN_CHANNELS..REAC_BOX_MAX_CHANNELS;
 *   - reac_frame_clean_len() strips the two-byte FCS residue, and only that: it
 *     strips 2 bytes exactly when the length is 2 more than a legal geometry.
 *
 * Each property's comment records a mutant (a one-line change that makes the
 * library wrong on purpose) and a seed in fuzz_decode_seed_corpus.zip that the
 * property catches it on.
 */
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include <reac/reac.h>
#include <reac/reac_braid.h>
#include <reac/reac_decode.h>
#include <reac/reac_encode.h>
#include <reac/reac_sample.h>
#include <reac/reac_upstream.h>

#include "fuzz.h"

/* 1 if a byte of the n-byte output is no longer the 0xa5 fill. */
static int changed(const uint8_t *p, size_t n)
{
	int c = 0;
	for (size_t i = 0; i < n; i++)
		c |= p[i] != 0xa5;
	return c;
}

/* Each decoded sample (ch, s) of an nch-wide region is the three bytes the braid
 * puts it in. The map is written out here from the header's statement of it, and
 * not taken from reac_braid_pos(), which the decoders and the encoder all read:
 * a wrong map there keeps the round trip below true.
 * contract: include/reac/reac_braid.h:9-12 (the pair (2k, 2k+1) of time sample s
 * is one 6-byte group at (s*n_ch + 2k)*3; the even channel's lo, mid, hi at
 * group[3], group[0], group[1], the odd channel's at group[4], group[5],
 * group[2]). */
static void check_braid(const uint8_t *audio, const uint8_t *pcm, int nch, int ns)
{
	int bad = 0;
	for (int ch = 0; ch < nch; ch++) {
		for (int s = 0; s < ns; s++) {
			const uint8_t *g = audio + ((size_t)s * (size_t)nch + (size_t)(ch & ~1)) * 3;
			const uint8_t *got = pcm + ((size_t)ch * (size_t)ns + (size_t)s) * REAC_RESOLUTION;
			if (ch & 1)
				bad |= got[0] != g[4] || got[1] != g[5] || got[2] != g[2];
			else
				bad |= got[0] != g[3] || got[1] != g[0] || got[2] != g[1];
		}
	}
	/* The decoders follow the documented braid, for every geometry they accept.
	 * A decoder accepts only nch * ns * 3 <= 1440, so each group lies inside the
	 * region.
	 * mutant: include/reac/reac_braid.h:60 `pos[0] = g + 3; pos[1] = g + 0;` -> `pos[0] = g + 0; pos[1] = g + 3;`
	 * input: downstream-program-48k
	 * mutant: include/reac/reac_braid.h:62 `pos[1] = g + 5; pos[2] = g + 2;` -> `pos[1] = g + 2; pos[2] = g + 5;`
	 * input: upstream-program-8ch
	 * mutant: src/reac_decode.c:78 `reac_braid_pos(s,` -> `reac_braid_pos(s % 12,`
	 * input: downstream-program-custom-20x24 */
	if (bad)
		abort();
}

/* Decode planar 24-bit PCM back to floats and braid it into a fresh region; the
 * region must come back as the frame carried it. */
static void check_round_trip(const uint8_t *audio, const uint8_t *pcm, int nch, int ns)
{
	size_t region = (size_t)nch * (size_t)ns * REAC_RESOLUTION;
	float *planes = malloc((size_t)nch * (size_t)ns * sizeof *planes);
	float **planar = malloc((size_t)nch * sizeof *planar);
	uint8_t *again = calloc(region ? region : 1, 1);
	/* not a property: an allocation failed */
	if (!planes || !planar || !again)
		abort();
	for (int ch = 0; ch < nch; ch++) {
		planar[ch] = planes + (size_t)ch * (size_t)ns;
		for (int s = 0; s < ns; s++)
			planar[ch][s] = reac_s24le_to_f32(pcm + ((size_t)ch * (size_t)ns + (size_t)s) * 3);
	}
	reac_braid_encode(again, nch, planar, nch, ns);
	/* The braid is a bijection over the n_ch x ns x 3 region and the 24-bit codec
	 * is exact, so decode followed by encode is the identity.
	 * mutant: src/reac_decode.c:79 `audio[pos[0]]` -> `audio[pos[1]]`
	 * input: downstream-program-48k
	 * mutant: src/reac_upstream.c:55 `audio[pos[0]]` -> `audio[pos[1]]`
	 * input: upstream-s0808-8ch */
	if (memcmp(again, audio, region) != 0)
		abort();
	free(again);
	free(planar);
	free(planes);
}

static void fuzz_downstream(const uint8_t *frame, size_t len, const struct reac_mode *mode)
{
	const int nch = mode->n_channels, ns = mode->samples_per_pkt;
	const int fits = nch > 0 && ns > 0 &&
	                 (size_t)nch * (size_t)ns * REAC_RESOLUTION <= (size_t)REAC_AUDIO_BYTES;
	/* The output holds the whole geometry the descriptor names (at most
	 * 127 x 127 x 3 bytes), also when it does not fit the region. So a decoder
	 * that wrongly accepts a wide geometry gives a wrong return value that a
	 * property sees, and a write past that geometry is still a sanitizer report.
	 * A write by a refused decode stays inside the buffer, so the buffer is filled
	 * with 0xa5 before each decode, and a refused decode must leave it so. */
	const size_t out_len = (nch > 0 && ns > 0) ? (size_t)nch * (size_t)ns * REAC_RESOLUTION : 0;
	const size_t olen = out_len ? out_len : 1;
	uint8_t *out = malloc(olen);
	/* not a property: an allocation failed */
	if (!out)
		abort();

	struct reac_frame f = reac_frame_inspect(frame, len, mode);
	const int wellformed = len == REAC_FRAME_BYTES && frame[12] == 0x88 && frame[13] == 0x19 &&
	                       frame[len - 2] == REAC_END_MARKER_0 && frame[len - 1] == REAC_END_MARKER_1;
	/* inspect's contract (reac_decode.h): valid is 1 only on a well-formed 0x8819
	 * frame of 1492 bytes that ends C2 EA, and 0 on every other frame.
	 * mutant: src/reac_decode.c:27 `f.valid = 1` -> `f.valid = 0`
	 * input: downstream-program-48k
	 * mutant: src/reac_decode.c:18 `len != (size_t)REAC_FRAME_BYTES` -> `len < (size_t)REAC_FRAME_BYTES`
	 * input: upstream-width-42
	 * mutant: src/reac_decode.c:21 `|| raw[13] != 0x19` -> ``
	 * input: downstream-bad-ethertype
	 * mutant: src/reac_decode.c:24 `|| raw[len - 1] != REAC_END_MARKER_1` -> ``
	 * input: downstream-bad-end-marker */
	if (f.valid != wellformed)
		abort();
	if (f.valid) {
		const uint16_t counter = (uint16_t)(frame[14] | frame[15] << 8);
		/* The counter is bytes 14-15 little-endian, in inspect and in
		 * reac_frame_counter() both.
		 * mutant: src/reac_decode.c:26 `raw[14] | (raw[15] << 8)` -> `raw[15] | (raw[14] << 8)`
		 * input: downstream-program-48k
		 * mutant: src/reac.c:60 `<< 8` -> `<< 7`
		 * input: downstream-program-48k */
		if (f.counter != counter || reac_frame_counter(frame) != counter)
			abort();
	}

	memset(out, 0xa5, olen);
	int r = reac_decode(frame, len, mode, out);
	/* The braid needs an even width and a geometry inside the region.
	 * mutant: src/reac_decode.c:84 `return ns;` -> `return ns - 1;`
	 * input: downstream-program-48k
	 * mutant: src/reac_decode.c:71 `(size_t)nch * (size_t)ns * REAC_RESOLUTION > (size_t)REAC_AUDIO_BYTES` -> `0`
	 * input: downstream-program-custom-42x12
	 * (This is the change of fuzz/sabotage/decode.patch. The ASan builds can
	 * report the read past the frame first; the plain build stops here.)
	 * mutant: src/reac_decode.c:70 `(nch & 1) ||` -> ``
	 * input: downstream-program-custom-39x12 */
	if (r != ((wellformed && fits && (nch & 1) == 0) ? ns : -1))
		abort();
	/* A refused reac_decode() writes nothing into the output.
	 * mutant: src/reac_decode.c:72 `return -1;` -> `return (out[0] = 1, out[1] = 1, out[2] = 1), -1;`
	 * input: downstream-program-custom-41x12
	 * mutant: src/reac_decode.c:60 `return -1;` -> `return (out[0] = 1, out[1] = 1, out[2] = 1), -1;`
	 * input: downstream-bad-ethertype */
	if (r < 0 && changed(out, olen))
		abort();
	/* reac_braid_encode() stops at 12 samples, so the round trip covers only a
	 * geometry of 12 samples or fewer; the braid check covers every one. */
	if (r > 0 && ns <= REAC_SAMPLES_PER_PKT)
		check_round_trip(frame + REAC_L2_HEADER_LEN, out, nch, ns);
	if (r > 0)
		check_braid(frame + REAC_L2_HEADER_LEN, out, nch, ns);

	memset(out, 0xa5, olen);
	r = reac_decode_plain_le(frame, len, mode, out);
	/* The plain-LE diagnostic pairs nothing, so only the size bound applies.
	 * mutant: src/reac_decode.c:123 `return ns;` -> `return ns - 1;`
	 * input: downstream-program-48k
	 * mutant: src/reac_decode.c:111 `(size_t)nch * (size_t)ns * REAC_RESOLUTION > (size_t)REAC_AUDIO_BYTES` -> `0`
	 * input: downstream-program-custom-41x12 */
	if (r != ((wellformed && fits) ? ns : -1))
		abort();
	/* A refused reac_decode_plain_le() writes nothing into the output.
	 * mutant: src/reac_decode.c:112 `return -1;` -> `return (out[0] = 1, out[1] = 1, out[2] = 1), -1;`
	 * input: downstream-program-custom-41x12
	 * mutant: src/reac_decode.c:101 `return -1;` -> `return (out[0] = 1, out[1] = 1, out[2] = 1), -1;`
	 * input: downstream-bad-ethertype */
	if (r < 0 && changed(out, olen))
		abort();
	if (r > 0) {
		const uint8_t *audio = frame + REAC_L2_HEADER_LEN;
		int bad = 0;
		for (int ch = 0; ch < nch; ch++)
			for (int s = 0; s < ns; s++)
				bad |= memcmp(out + ((size_t)ch * (size_t)ns + (size_t)s) * REAC_RESOLUTION,
				              audio + ((size_t)s * (size_t)nch + (size_t)ch) * REAC_RESOLUTION,
				              REAC_RESOLUTION) != 0;
		/* Its meaning, as the header defines it: (ch, s) is the straight copy at
		 * (s * n_channels + ch) * 3. Check each sample. r > 0 gives
		 * nch * ns <= 480.
		 * mutant: src/reac_decode.c:117 `(size_t)(s * nch + ch)` -> `(size_t)(ch * ns + s)`
		 * input: downstream-program-48k */
		if (bad)
			abort();
	}
	free(out);
}

static void fuzz_upstream(const uint8_t *frame, size_t len)
{
	int nch = reac_upstream_channels(len);
	/* The geometry of a clean frame, worked out here and not taken from a libreac
	 * function (reac_frame_channels() is one).
	 * contract: include/reac/reac.h:65-66 (52 bytes of header and end marker,
	 * then 36 bytes for each channel; any other length has no geometry) */
	const unsigned geom =
		len >= REAC_UPSTREAM_OVERHEAD && (len - REAC_UPSTREAM_OVERHEAD) % REAC_UPSTREAM_BYTES_PER_CH == 0
			? (unsigned)((len - REAC_UPSTREAM_OVERHEAD) / REAC_UPSTREAM_BYTES_PER_CH)
			: 0;
	const int box_width = geom >= REAC_BOX_MIN_CHANNELS && geom <= REAC_BOX_MAX_CHANNELS &&
	                      (geom & 1) == 0;
	/* A box's return is a legal geometry at a box width, and nothing else. A box
	 * width is a protocol fact: an even width from REAC_BOX_MIN_CHANNELS (2) to
	 * REAC_BOX_MAX_CHANNELS (40). The harness spells the rule out and does not ask
	 * reac_box_width_ok().
	 * contract: include/reac/reac_facts_box_width.h:43, :51 (2 and 40), and
	 * include/reac/reac.h:70-71 (even per direction)
	 * mutant: include/reac/reac.h:86 `n <= REAC_BOX_MAX_CHANNELS` -> `n <= REAC_BOX_MAX_CHANNELS + 2`
	 * input: upstream-width-42
	 * mutant: include/reac/reac.h:86 `&& (n & 1) == 0` -> ``
	 * input: upstream-width-3
	 * mutant: src/reac_upstream.c:25 `/ REAC_UPSTREAM_BYTES_PER_CH;` -> `/ REAC_UPSTREAM_BYTES_PER_CH + 2;`
	 * input: upstream-s0808-8ch */
	if (nch != (box_width ? (int)geom : -1))
		abort();

	size_t out_len = nch > 0 ? (size_t)nch * REAC_SAMPLES_PER_PKT * REAC_RESOLUTION : 0;
	const size_t olen = out_len ? out_len : 1;
	uint8_t *out = malloc(olen);
	/* not a property: an allocation failed */
	if (!out)
		abort();
	/* The output is filled with 0xa5, so a write by a refused call shows. */
	memset(out, 0xa5, olen);
	const int r_null_raw = reac_upstream_decode(NULL, len, out);
	const int r_null_out = reac_upstream_decode(frame, len, NULL);
	/* A NULL frame or a NULL output is refused, and the refused call with a NULL
	 * frame writes nothing into the output.
	 * mutant: src/reac_upstream.c:37 `return -1;` -> `return raw ? -1 : 0;`
	 * input: upstream-s0808-8ch
	 * mutant: src/reac_upstream.c:37 `return -1;` -> `return out ? -1 : 0;`
	 * input: upstream-s0808-8ch
	 * mutant: src/reac_upstream.c:37 `return -1;` -> `return (out ? (out[0] = 1) : 0), -1;`
	 * input: upstream-s0808-8ch */
	if (r_null_raw != -1 || r_null_out != -1 || changed(out, olen))
		abort();
	int r = reac_upstream_decode(frame, len, out);
	int ok = nch > 0 && frame[12] == 0x88 && frame[13] == 0x19 &&
	         frame[len - 2] == REAC_END_MARKER_0 && frame[len - 1] == REAC_END_MARKER_1;
	/* A return decodes exactly when it is at a box width, has EtherType 88 19 and
	 * ends C2 EA.
	 * mutant: src/reac_upstream.c:41 `|| raw[13] != 0x19` -> ``
	 * input: upstream-bad-ethertype
	 * mutant: src/reac_upstream.c:45 `|| raw[len - 1] != REAC_END_MARKER_1` -> ``
	 * input: upstream-bad-end-marker */
	if (r != (ok ? REAC_SAMPLES_PER_PKT : -1))
		abort();
	/* A refused reac_upstream_decode() writes nothing into the output.
	 * mutant: src/reac_upstream.c:42 `return -1;` -> `return (out[0] = 1, out[1] = 1, out[2] = 1), -1;`
	 * input: upstream-bad-ethertype
	 * mutant: src/reac_upstream.c:46 `return -1;` -> `return (out[0] = 1, out[1] = 1, out[2] = 1), -1;`
	 * input: upstream-bad-end-marker */
	if (r < 0 && changed(out, olen))
		abort();
	if (r > 0) {
		check_round_trip(frame + REAC_L2_HEADER_LEN, out, nch, REAC_SAMPLES_PER_PKT);
		check_braid(frame + REAC_L2_HEADER_LEN, out, nch, REAC_SAMPLES_PER_PKT);
	}
	free(out);
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	if (size >= FUZZ_INPUT_MAX)
		return 0;
	struct fuzz_in in = fuzz_in(data, size);
	uint8_t sel = fuzz_u8(&in);
	int8_t nch = (int8_t)fuzz_u8(&in);
	int8_t ns = (int8_t)fuzz_u8(&in);

	struct reac_mode custom = { 48000, nch, ns };
	const struct reac_mode *mode;
	switch (sel & 3) {
	case 0:  mode = &REAC_MODE_44K1; break;
	case 1:  mode = &REAC_MODE_48K;  break;
	case 2:  mode = &REAC_MODE_96K;  break;
	default: mode = &custom;         break;
	}

	const uint8_t *body;
	size_t len = fuzz_take(&in, in.n, &body);
	uint8_t *frame = fuzz_dup(body, len);

	int is_reac = reac_frame_is_reac(frame, len);
	/* The helpers every ingest door calls first.
	 * mutant: src/reac.c:54 `frame[13] == 0x19` -> `frame[13] == 0x18`
	 * input: downstream-program-48k */
	if (is_reac != (len >= 14 && frame[12] == 0x88 && frame[13] == 0x19))
		abort();
	size_t clean = reac_frame_clean_len(len);
	/* Only the +2 FCS residue is ever stripped, and only off a length that is a
	 * legal geometry once it is gone.
	 * mutant: src/reac.c:75 `len - 2` -> `len - 1`
	 * input: downstream-fcs-residue */
	if (clean != len &&
	    (clean + 2 != len || clean < REAC_UPSTREAM_OVERHEAD ||
	     (clean - REAC_UPSTREAM_OVERHEAD) % REAC_UPSTREAM_BYTES_PER_CH != 0))
		abort();
	const int residue = len >= REAC_UPSTREAM_OVERHEAD + 2 &&
	                    (len - REAC_UPSTREAM_OVERHEAD) % REAC_UPSTREAM_BYTES_PER_CH == 2;
	/* And the residue is always stripped: a length that is 2 more than a legal
	 * geometry (reac.c: congruent to 2 mod 36 past the 52-byte overhead) comes
	 * back changed, and every other length comes back as it is.
	 * mutant: src/reac.c:75 `return len - 2;` -> `return len;`
	 * input: downstream-fcs-residue */
	if (residue != (clean != len))
		abort();

	fuzz_downstream(frame, len, mode);
	fuzz_upstream(frame, len);
	free(frame);
	return 0;
}
