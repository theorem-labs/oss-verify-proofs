// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>

/* libFuzzer harness: the sample-rate converter (omx_src.h): a rate pair reduced to a plan, the
 * polyphase table designed, a take converted block by block and flushed.
 *
 * Input:  [0..3]  the source rate, u32 LE (any value: 0 and the absurd are refused)
 *         [4..7]  the destination rate, u32 LE
 *         [8]     bit 0: the blocks are cut at the sizes the following bytes give, else the
 *                 take goes through in one call; bit 1: the take is flushed at its end
 *         [9..]   blocks until the input ends or 16 have run: a u16 length (modulo 513, a
 *                 length of 0 is a block of no samples) and that many finite samples
 *                 (fuzz_block, a signed 16-bit word each).
 *
 * The plan refuses what it cannot size (a zero rate, an interpolation factor past OMX_SRC_MAX_L),
 * and the harness holds it to refusing exactly that; a refused plan ends the input.
 *
 * Properties, each an abort():
 *   - the plan is taken exactly when both rates are above 0 and out / gcd(out, in) is at most
 *     OMX_SRC_MAX_L;
 *   - the plan is the REDUCED ratio: l/m equals out/in, and gcd(l, m) is 1;
 *   - the coefficients of each phase of the table sum to 1, to float rounding;
 *   - a call never makes more outputs than omx_src_out_capacity() allows for its input, and a take run
 *     without a flush makes no more than a whole file's omx_src_out_frames() plus the filter's half
 *     length (the outputs its first samples wait for);
 *   - the take is the same however it is cut into blocks: run whole, or in the blocks the input
 *     gives, it yields the same samples bit for bit;
 *   - every output sample is finite, and bounded by the input's peak times the filter's own
 *     worst-case gain (the sum of the absolute coefficients of its worst phase);
 *   - an identity plan (the same rate) returns the input samples unchanged.
 */
#define OMX_CONTRACT_STORAGE 1
#include <omxdsp/omx_src.h>

#include "fuzz.h"

#define BLOCKS_MAX 16
#define BLOCK_MAX 512u
#define IN_MAX (BLOCKS_MAX * BLOCK_MAX)

/* the harness's own gcd: the plan is held to this, not to the library's */
static uint32_t gcd(uint32_t a, uint32_t b) {
  while (b != 0u) {
    const uint32_t t = a % b;
    a = b;
    b = t;
  }
  return a;
}

/* a take: the input samples as the blocks gave them, and where each block ends */
struct take {
  float x[IN_MAX];
  uint32_t end[BLOCKS_MAX];
  int blocks;
  uint32_t n;
};

static uint32_t convert(const struct omx_src_plan *p, const float *coef, const struct take *t, int whole, int flush,
                        float *out, uint32_t cap) {
  float hist[OMX_SRC_TAPS];
  struct omx_src s;
  omx_src_init(&s, p, coef, hist);
  uint32_t w = 0, from = 0;
  if (whole) {
    w = omx_src_run(&s, t->x, t->n, out, cap, flush);
  } else {
    for (int b = 0; b < t->blocks; b++) {
      const int last = b == t->blocks - 1;
      const uint32_t n = t->end[b] - from;
      w += omx_src_run(&s, t->x + from, n, out + w, cap - w, last && flush);
      from = t->end[b];
    }
  }
  return w;
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  struct fuzz_in in = fuzz_in(data, size);
  const uint32_t rin = fuzz_u32(&in), rout = fuzz_u32(&in);
  const uint8_t flags = fuzz_u8(&in);
  fuzz_ledger_reset();

  struct omx_src_plan p;
  if (omx_src_plan_of(rin, rout, &p) != 0) {
    /* The plan refuses only what it cannot size: a zero rate, or an interpolation factor past the limit.
     * mutant: include/omxdsp/omx_src.h:89 `l > OMX_SRC_MAX_L` -> `l > 1u`
     * input: 44100-48000 */
    if (!(rin == 0 || rout == 0 || rout / gcd(rout, rin) > OMX_SRC_MAX_L)) {
      FUZZ_SAY("the plan refused %u -> %u, which it can size", (unsigned)rin, (unsigned)rout);
      abort();
    }
    return 0;
  }
  /* A plan taken is one that can be sized: neither rate is 0, and the factor is inside the limit.
   * mutant: include/omxdsp/omx_src.h:89 `l > OMX_SRC_MAX_L` -> `l > 2u * OMX_SRC_MAX_L`
   * input: one-to-1025 */
  if (!(rin != 0 && rout != 0 && rout / gcd(rout, rin) <= OMX_SRC_MAX_L)) {
    FUZZ_SAY("the plan took %u -> %u, past the limit of %u", (unsigned)rin, (unsigned)rout, (unsigned)OMX_SRC_MAX_L);
    abort();
  }
  /* The plan is reduced, by the harness's own gcd.
   * mutant: include/omxdsp/omx_src.h:86 `omx_src_gcd(out_rate, in_rate)` -> `1u`
   * input: six-to-four */
  if (!(gcd(p.l, p.m) == 1u)) {
    FUZZ_SAY("the plan %u/%u of %u -> %u is not reduced", (unsigned)p.l, (unsigned)p.m, (unsigned)rin, (unsigned)rout);
    abort();
  }
  /* The plan is the ratio of the two rates.
   * mutant: include/omxdsp/omx_src.h:88 `in_rate / g` -> `in_rate / g + 2u`
   * input: 44100-48000 */
  if (!((uint64_t)p.l * rin == (uint64_t)p.m * rout)) {
    FUZZ_SAY("the plan %u/%u is not the ratio of %u -> %u", (unsigned)p.l, (unsigned)p.m, (unsigned)rin, (unsigned)rout);
    abort();
  }
  const size_t ncoef = omx_src_coef_count(&p);
  float *coef = malloc(ncoef * sizeof(float));
  /* not a property: malloc failed */
  if (!coef) abort();
  omx_src_design(&p, coef, OMX_SRC_ROLLOFF_DOUBLE, OMX_SRC_STOPBAND_DB);

  static struct take t;
  t.n = 0;
  t.blocks = 0;
  float peak = 0.0f;
  while (t.blocks < BLOCKS_MAX && in.n > 0) {
    const uint32_t n = fuzz_u16(&in) % (BLOCK_MAX + 1u);
    fuzz_block(&in, t.x + t.n, n, 0);
    for (uint32_t i = 0; i < n; i++) peak = fmaxf(peak, fabsf(t.x[t.n + i]));
    t.n += n;
    t.end[t.blocks++] = t.n;
  }

  if (t.blocks == 0) t.end[t.blocks++] = 0u; /* a take is at least one call, of no samples */

  /* the worst phase's gain: the sum of the absolute coefficients, what no output can exceed per unit of peak */
  double gain = 0.0;
  for (uint32_t ph = 0; ph < p.l; ph++) {
    double g = 0.0;
    for (uint32_t k = 0; k < p.taps; k++) g += fabs((double)coef[(size_t)ph * p.taps + k]);
    if (g > gain) gain = g;
  }

  const uint32_t cap = omx_src_out_capacity(&p, t.n + 2u * p.taps);
  float *a = malloc((size_t)cap * sizeof(float) + 1), *b = malloc((size_t)cap * sizeof(float) + 1);
  /* not a property: malloc failed */
  if (!a || !b) abort();
  const int flush = (flags >> 1) & 1;
  const uint32_t wa = convert(&p, coef, &t, 1, flush, a, cap);
  const uint32_t wb = convert(&p, coef, &t, (flags & 1u) ? 0 : 1, flush, b, cap);

  /* A take is the same however it is cut into blocks, bit for bit.
   * mutant: include/omxdsp/omx_src.h:331 `i < in_n` -> `i + 1u < in_n`
   * input: 44100-48000 */
  if (!(wa == wb && memcmp(a, b, (size_t)wa * sizeof(float)) == 0)) {
    FUZZ_SAY("%u -> %u: the take cut into %d blocks is not the take run whole (%u and %u samples)", (unsigned)rin, (unsigned)rout, t.blocks, (unsigned)wa, (unsigned)wb);
    abort();
  }
  const uint64_t want = omx_src_out_frames(t.n, &p);
  if (!flush) {
    /* Without a flush, a take makes no more than a whole file's frames and the half length of the filter.
     * mutant: include/omxdsp/omx_src.h:309 `s->acc += (uint64_t)s->m` -> `s->acc += (uint64_t)s->m / 2u`
     * input: 96000-48000 */
    if (!(wa <= want + p.taps / 2u + 1u)) {
      FUZZ_SAY("%u -> %u: %u samples out of %u in, a whole file is %u", (unsigned)rin, (unsigned)rout, (unsigned)wa, (unsigned)t.n, (unsigned)want);
      abort();
    }
  }
  /* A take makes no more samples than the capacity of what went in.
   * mutant: include/omxdsp/omx_src.h:309 `s->acc += (uint64_t)s->m` -> `s->acc += (uint64_t)s->m / 2u`
   * input: 48000-44100 */
  if (!(wa <= omx_src_out_capacity(&p, t.n + (flush ? p.taps : 0u)))) {
    FUZZ_SAY("%u -> %u: %u samples out of %u in exceeds the capacity", (unsigned)rin, (unsigned)rout, (unsigned)wa, (unsigned)t.n);
    abort();
  }
  for (uint32_t i = 0; i < wa; i++) {
    /* Each output is finite, and inside the input's peak times the filter's worst gain.
     * mutant: include/omxdsp/omx_src.h:281 `c[k] * h[k]` -> `1000.0f * c[k] * h[k]`
     * input: 44100-48000 */
    if (!(isfinite(a[i]) && fabs((double)a[i]) <= gain * (double)peak * 1.0001 + 1e-30)) {
      FUZZ_SAY("%u -> %u: output %u is %g, past %g x peak %g", (unsigned)rin, (unsigned)rout, (unsigned)i, (double)a[i], gain, (double)peak);
      abort();
    }
  }
  if (p.l == 1u && p.m == 1u)
    /* An identity plan returns the take unchanged.
     * mutant: include/omxdsp/omx_src.h:168 `coef[0] = 1.0f` -> `coef[0] = 0.5f`
     * input: 48000-48000 */
    if (!(wa >= t.n && memcmp(a, t.x, (size_t)t.n * sizeof(float)) == 0)) {
      FUZZ_SAY("an identity plan changed the take");
      abort();
    }
  for (uint32_t ph = 0; ph < p.l; ph++) {
    double sum = 0.0;
    for (uint32_t k = 0; k < p.taps; k++) sum += (double)coef[(size_t)ph * p.taps + k];
    /* The coefficients of each phase sum to 1, the rule of the table in omx_src.h. The bound on the
     * outputs above takes its gain from this table, so this is what holds the table's scale.
     * mutant: include/omxdsp/omx_src.h:201 `*= g;` -> `*= 2.0f * g;`
     * input: 44100-48000 */
    if (!(fabs(sum - 1.0) <= 1e-4)) {
      FUZZ_SAY("%u -> %u: phase %u of the table sums to %g", (unsigned)rin, (unsigned)rout, (unsigned)ph, sum);
      abort();
    }
  }
  fuzz_ledger_clean("src");
  free(coef);
  free(a);
  free(b);
  return 0;
}
