// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>

/* libFuzzer harness: the two delay lines, the fractional one (omx_fdelay.h, a Lagrange kernel
 * over a caller-owned ring) and the integer one (omx_idelay.h, a ring with a cross-fade between
 * two delays).
 *
 * Input:  [0]     bit 0: the line is fractional, else integer; bit 1: the order is 5, else 3
 *                 (fractional); bit 2: the blocks' samples are mono, else the integer pair runs
 *                 both legs; bit 3: the fractional line's order is the signed byte after the size;
 *                 bit 4: each block of the integer line starts with a raw float of ms and a raw
 *                 float of rate, for omx_idelay_samples() alone
 *         [1..2]  u16 LE: the ring's size in samples (1..4096; refused sizes are part of the story)
 *         [3..]   the order, when bit 3 asks for it; then blocks until the input ends or 12 have run: a u8 block length (1..128), the
 *                 delay for the block (the fractional line: any float, NaN and the infinities
 *                 included; the integer line: a u16 of tenths of a millisecond at a rate the
 *                 next byte picks off the grid) and the block's samples (fuzz_block, finite).
 *
 * The ring starts zeroed, so the line is silent before the take starts, and the harness keeps the
 * whole take itself, which is the independent oracle: the line's own ring is never read back. It
 * also works out itself, from the request and the rule in the comment of omx_fdelay_latency(), the
 * delay a line owes, its whole part, its fraction and the Lagrange weights at that fraction; and
 * it keeps the integer pair's last delays, starting at 0, rather than read the line's.
 *
 * Properties, each an abort():
 *   - a refused order or ring (init) leaves the line unarmed, and an unarmed line leaves the block
 *     as it was; an armed line's delay lands in [0, the ring's longest], a non-finite request
 *     reads as 0;
 *   - a WHOLE-sample delay is exact: the block's output is the take delayed by that many samples,
 *     bit for bit, zero before the start of the take;
 *   - a fractional delay stays finite and inside the interpolation's own bound: the sum of the
 *     absolute Lagrange weights at that fraction times the take's peak; and each sample is the
 *     Lagrange sum over the harness's copy of the take, to a tolerance;
 *   - a steady integer delay (the same one two blocks running) is the take delayed, bit for bit;
 *     a delay change (the cross-fade) stays between the two taps it fades;
 *   - omx_idelay_samples() is the rounded delay, saturated at cap - 1, for any finite ms and any
 *     finite rate off the declared grid or on it, and 0 for a delay of no length.
 */
#define OMX_CONTRACT_STORAGE 1
#include <omxdsp/omx_fdelay.h>
#include <omxdsp/omx_idelay.h>

#include "fuzz.h"

#define BLOCKS_MAX 12
#define BLOCK_MAX 128u
#define TAKE_MAX (BLOCKS_MAX * BLOCK_MAX)
#define RING_MAX 4096u

static float take_at(const float *take, long i) { return i < 0 ? 0.0f : take[i]; }

/* The delay in samples: the nearest whole sample, 0 for no ms or no rate, and the ring's last slot
 * for anything past it, however large. The rule in the comment of omx_idelay_samples(). */
static uint32_t samples_owed(float ms, float sr, uint32_t cap) {
  if (!(ms > 0.0f) || !(sr > 0.0f)) return 0u;
  const float s = ms * sr * 0.001f + 0.5f;
  return s >= (float)cap ? cap - 1u : (uint32_t)s;
}

/* A ring's longest delay at an order: the ring less the kernel's reach, the lookbehind and two. */
static float longest(uint32_t cap, int order) {
  const uint32_t reach = (uint32_t)(order - 1) / 2u + 2u;
  return cap <= reach ? 0.0f : (float)(cap - reach);
}

/* The delay a line owes a request: not finite reads as 0, below 0 as 0, a fractional one below the
 * lookbehind as the lookbehind, and then no more than the ring's longest. */
static float owed(float request, uint32_t cap, int order) {
  float d = request - request == 0.0f ? request : 0.0f;
  if (d < 0.0f) d = 0.0f;
  const float shortest = (float)((order - 1) / 2);
  if (d < shortest && d != floorf(d)) d = shortest;
  if (d > longest(cap, order)) d = longest(cap, order);
  return d;
}

/* The Lagrange weights at the place kf past the tap at local index (order - 1) / 2. Returns their
 * absolute sum: what a sample can grow by. */
static double weights(int order, float kf, double *w) {
  double s = 0.0;
  for (int k = 0; k <= order; k++) {
    w[k] = 1.0;
    for (int j = 0; j <= order; j++)
      if (j != k) w[k] *= ((double)kf - (double)(j - (order - 1) / 2)) / (double)(k - j);
    s += fabs(w[k]);
  }
  return s;
}

static void fractional(struct fuzz_in *in, int order, uint32_t cap) {
  float *ring = calloc(cap ? cap : 1u, sizeof(float));
  /* not a property: calloc failed */
  if (!ring) abort();
  struct omx_fdelay l;
  const int order_ok = order == 3 || order == 5; /* an odd order the kernel has */
  const int fits = order_ok && cap > (uint32_t)(order - 1) / 2u + 2u; /* the kernel's reach: the lookbehind and two */
  const enum omx_fdelay_code code = omx_fdelay_init(&l, ring, cap, order);
  const int armed = code == OMX_FDELAY_OK;
  /* A ring takes a line exactly when it is longer than the kernel's reach: the lookbehind and two.
   * mutant: include/omxdsp/omx_fdelay.h:139 `omx_fdelay_max_delay(cap, order) <= 0.0f` -> `cap < 2000u`
   * input: fractional-3 */
  if (!(armed == fits)) {
    FUZZ_SAY("init answered %d for a ring of %u at order %d", (int)code, (unsigned)cap, order);
    abort();
  }
  if (!order_ok) {
    /* An order the kernel does not have is answered by the code that says so.
     * mutant: include/omxdsp/omx_fdelay.h:138 `return OMX_FDELAY_BAD_ORDER` -> `return OMX_FDELAY_RING_TOO_SMALL`
     * input: fractional-refused-order */
    if (!(code == OMX_FDELAY_BAD_ORDER)) {
      FUZZ_SAY("order %d was answered %d", order, (int)code);
      abort();
    }
    fuzz_ledger_reset();
  } else if (!fits) {
    /* a ring that cannot hold the kernel is refused by a code, and the call records its PRE `the-ring-holds-the-kernels-reach` */
    /* A ring that cannot hold the kernel is answered by the code that says so.
     * mutant: include/omxdsp/omx_fdelay.h:139 `return OMX_FDELAY_RING_TOO_SMALL` -> `return OMX_FDELAY_BAD_ORDER`
     * input: fractional-tiny-ring */
    if (!(code == OMX_FDELAY_RING_TOO_SMALL)) {
      FUZZ_SAY("a ring of %u at order %d was answered %d", (unsigned)cap, order, (int)code);
      abort();
    }
    fuzz_ledger_reset();
  }
  if (!armed) {
    /* A refused line is left unarmed.
     * mutant: include/omxdsp/omx_fdelay.h:137 `l->order = 0;` -> `l->order = order;`
     * input: fractional-refused-order */
    if (!(l.order == 0 && l.ring == NULL && l.cap == 0u)) {
      FUZZ_SAY("a line refused with %d has order %d and a ring of %u", (int)code, l.order, (unsigned)l.cap);
      abort();
    }
  }
  static float take[TAKE_MAX];
  uint32_t done = 0;
  float peak = 0.0f;
  for (int b = 0; b < BLOCKS_MAX && in->n > 0; b++) {
    const uint32_t n = 1u + fuzz_u8(in) % BLOCK_MAX;
    const float delay = fuzz_f32(in);
    float buf[BLOCK_MAX], dry[BLOCK_MAX];
    fuzz_block(in, buf, n, 0);
    memcpy(dry, buf, n * sizeof(float));
    for (uint32_t i = 0; i < n; i++) {
      take[done + i] = buf[i];
      peak = fmaxf(peak, fabsf(buf[i]));
    }
    if (!armed) {
      /* an unarmed line is not run: omx_fdelay_process requires a line that is armed (its PRE) */
      /* A line that is not armed delays nothing.
       * mutant: include/omxdsp/omx_fdelay.h:229 `return 0.0f` -> `return 1.0f`
       * input: fractional-tiny-ring */
      if (!(omx_fdelay_latency(&l, delay) == 0.0f)) {
        FUZZ_SAY("an unarmed line has a latency");
        abort();
      }
      omx_fdelay_process(buf, n, &l, delay);
      fuzz_ledger_reset(); /* the call records its PRE `line-is-armed`: the harness made this one on purpose */
      /* A line that is not armed leaves the block as it was, bit for bit.
       * mutant: include/omxdsp/omx_fdelay.h:451 `return;` -> `{ if (buf) buf[0] = 0.0f; return; }`
       * input: fractional-refused-order */
      if (!(memcmp(buf, dry, n * sizeof(float)) == 0)) {
        FUZZ_SAY("an unarmed line changed the block");
        abort();
      }
      done += n;
      continue;
    }
    const float d = omx_fdelay_latency(&l, delay);
    /* A delay is delivered inside the ring, and finite.
     * mutant: include/omxdsp/omx_fdelay.h:235 `d = maxd;` -> `;`
     * input: fractional-3 */
    if (!(d >= 0.0f && d <= longest(cap, order) && d - d == 0.0f)) {
      FUZZ_SAY("a request of %g was delivered as %g, in a ring that serves %g", (double)delay, (double)d, (double)longest(cap, order));
      abort();
    }
    if (!(delay - delay == 0.0f)) {
      /* A delay that is not finite reads as 0.
       * mutant: include/omxdsp/omx_fdelay.h:230 `: 0.0f` -> `: 1.0f`
       * input: fractional-3 */
      if (!(d == 0.0f)) {
        FUZZ_SAY("a non-finite request was delivered as %g", (double)d);
        abort();
      }
    }
    /* A line delivers what its comment says it owes a request.
     * mutant: include/omxdsp/omx_fdelay.h:234 `d = mind;` -> `;`
     * input: fractional-3 */
    if (!(d == owed(delay, cap, order))) {
      FUZZ_SAY("a request of %g was delivered as %g, the rule says %g", (double)delay, (double)d, (double)owed(delay, cap, order));
      abort();
    }
    omx_fdelay_process(buf, n, &l, delay);
    /* the read, from what the harness says is owed: the whole part, the fraction from the older tap */
    const float own = owed(delay, cap, order);
    const uint32_t id = (uint32_t)own;
    const float fr = own - (float)id, kf = 1.0f - fr;
    const int whole = fr == 0.0f || kf >= 1.0f;
    double w[OMX_FDELAY_MAX_TAPS];
    const double bound = whole ? 1.0 : weights(order, kf, w);
    for (uint32_t i = 0; i < n; i++) {
      /* The line gives finite samples for finite samples.
       * mutant: include/omxdsp/omx_fdelay.h:459 `omx_fdelay_read_at(l, id, whole ? 0 : c)` -> `NAN`
       * input: fractional-3 */
      if (!(buf[i] - buf[i] == 0.0f)) {
        FUZZ_SAY("fractional delay %g gave a non-finite sample at %u", (double)d, (unsigned)i);
        abort();
      }
      /* A sample stays inside the sum of the absolute Lagrange weights times the take's peak.
       * mutant: include/omxdsp/omx_fdelay.h:459 `omx_fdelay_read_at(l, id, whole ? 0 : c)` -> `8.0f * omx_fdelay_read_at(l, id, whole ? 0 : c)`
       * input: fractional-3 */
      if (!(fabs((double)buf[i]) <= bound * (double)peak * 1.0001 + 1e-30)) {
        FUZZ_SAY("delay %g (%g weights): sample %u is %g, past %g x peak %g", (double)d, bound, (unsigned)i, (double)buf[i], bound, (double)peak);
        abort();
      }
      if (whole) {
        const float want = take_at(take, (long)(done + i) - (long)id);
        /* A whole-sample delay is the take delayed, bit for bit.
         * mutant: include/omxdsp/omx_fdelay.h:459 `omx_fdelay_read_at(l, id, whole` -> `omx_fdelay_read_at(l, id + 1u, whole`
         * input: fractional-3
         * mutant: include/omxdsp/omx_fdelay.h:254 `*id = (uint32_t)d;` -> `*id = (uint32_t)d + 1u;`
         * input: fractional-3 */
        if (!(memcmp(&want, &buf[i], sizeof want) == 0 || (want == 0.0f && buf[i] == 0.0f))) {
          FUZZ_SAY("whole delay %u: sample %u is %g, the take says %g", (unsigned)id, (unsigned)(done + i), (double)buf[i], (double)want);
          abort();
        }
      } else {
        /* the kernel's order + 1 taps, oldest first, the oldest one past the lookbehind behind the whole part */
        const long oldest = (long)(done + i) - (long)id - (long)((order - 1) / 2) - 1L;
        double want = 0.0;
        for (int k = 0; k <= order; k++) want += w[k] * (double)take_at(take, oldest + k);
        /* A fractional delay is the Lagrange sum over the take, to float rounding.
         * mutant: include/omxdsp/omx_fdelay.h:256 `*kf = 1.0f - fr;` -> `*kf = fr;`
         * input: fractional-3 */
        if (!(fabs((double)buf[i] - want) <= 1e-5 * bound * (double)peak + 1e-12)) {
          FUZZ_SAY("delay %g: sample %u is %g, the Lagrange sum is %g", (double)own, (unsigned)(done + i), (double)buf[i], want);
          abort();
        }
      }
    }
    done += n;
  }
  free(ring);
}

static void integer(struct fuzz_in *in, uint32_t cap, int mono, int any_word) {
  float *rl = calloc(cap + 1u, sizeof(float)), *rr = calloc(cap + 1u, sizeof(float));
  /* not a property: calloc failed */
  if (!rl || !rr) abort();
  struct omx_idelay_pair d = {rl, rr, cap, 0, 0, 0, 0};
  static float takel[TAKE_MAX], taker[TAKE_MAX];
  uint32_t done = 0;
  uint32_t last_l = 0, last_r = 0;
  for (int b = 0; b < BLOCKS_MAX && in->n > 0; b++) {
    const uint32_t n = 1u + fuzz_u8(in) % BLOCK_MAX;
    if (any_word) {
      const float any_ms = fuzz_f32(in), any_sr = fuzz_f32(in);
      if (any_ms - any_ms == 0.0f && any_sr - any_sr == 0.0f) {
        const uint32_t got = omx_idelay_samples(any_ms, any_sr, cap);
        fuzz_ledger_reset(); /* the call records its PRE `rate-is-declared`: the harness made this one on purpose */
        /* A delay in samples lands inside the ring for any finite ms and rate.
         * mutant: include/omxdsp/omx_idelay.h:67 `d = d >= cap ? cap - 1 : d;` -> `d = d >= cap && s < 1.0e7f ? cap - 1 : d;`
         * input: integer-any-ms-and-rate */
        if (!(got < cap)) {
          FUZZ_SAY("omx_idelay_samples(%g ms, %g, %u) = %u is outside the ring", (double)any_ms, (double)any_sr, (unsigned)cap, (unsigned)got);
          abort();
        }
        /* It is the rounded delay, saturated at the ring's last slot, however large the request.
         * mutant: include/omxdsp/omx_idelay.h:66 `s >= (float)cap ? cap : (uint32_t)s` -> `s >= (float)cap ? 0u : (uint32_t)s`
         * input: integer-any-ms-and-rate */
        if (!(got == samples_owed(any_ms, any_sr, cap))) {
          FUZZ_SAY("omx_idelay_samples(%g ms, %g, %u) = %u, the rule says %u", (double)any_ms, (double)any_sr, (unsigned)cap, (unsigned)got, (unsigned)samples_owed(any_ms, any_sr, cap));
          abort();
        }
      }
    }
    const float sr = OMX_DECLARED_RATES[fuzz_below(in, OMX_DECLARED_RATE_COUNT)];
    const float ms_l = (float)fuzz_u16(in) * 0.1f, ms_r = (float)fuzz_u16(in) * 0.1f;
    const uint32_t tl = omx_idelay_samples(ms_l, sr, cap), tr = omx_idelay_samples(ms_r, sr, cap);
    /* A delay in samples lands inside the ring, on both legs.
     * mutant: include/omxdsp/omx_idelay.h:67 `cap - 1 : d` -> `d : d`
     * input: integer-pair */
    if (!(tl < cap && tr < cap)) {
      FUZZ_SAY("omx_idelay_samples(%g ms, %g, %u) = %u / %u is outside the ring", (double)ms_l, (double)sr, (unsigned)cap, (unsigned)tl, (unsigned)tr);
      abort();
    }
    if (ms_l == 0.0f) {
      /* A delay of no length is 0 samples.
       * mutant: include/omxdsp/omx_idelay.h:63 `return 0;` -> `return 1;`
       * input: integer-pair */
      if (!(tl == 0u)) {
        FUZZ_SAY("a delay of no length is %u samples", (unsigned)tl);
        abort();
      }
    }
    /* A delay in samples is the rounded delay, on both legs.
     * mutant: include/omxdsp/omx_idelay.h:64 `* 0.001f` -> `* 0.002f`
     * input: integer-pair */
    if (!(tl == samples_owed(ms_l, sr, cap) && tr == samples_owed(ms_r, sr, cap))) {
      FUZZ_SAY("omx_idelay_samples(%g, %g ms, %g, %u) = %u / %u, the rule says %u / %u", (double)ms_l, (double)ms_r, (double)sr, (unsigned)cap, (unsigned)tl, (unsigned)tr, (unsigned)samples_owed(ms_l, sr, cap), (unsigned)samples_owed(ms_r, sr, cap));
      abort();
    }
    float l[BLOCK_MAX], r[BLOCK_MAX];
    fuzz_block(in, l, n, 0);
    fuzz_block(in, r, n, 0);
    for (uint32_t i = 0; i < n; i++) {
      takel[done + i] = l[i];
      taker[done + i] = r[i];
    }
    /* a steady delay is exact; one that moves is a cross-fade between the old tap and the new one */
    const int steady_l = last_l == tl, steady_r = last_r == tr;
    const uint32_t from_l = last_l, from_r = last_r;
    omx_idelay_pair_apply(l, mono ? NULL : r, n, &d, tl, tr);
    for (uint32_t i = 0; i < n; i++) {
      const float wl = take_at(takel, (long)(done + i) - (long)tl);
      const float ol = take_at(takel, (long)(done + i) - (long)from_l);
      if (steady_l) {
        /* A steady delay on the left is the take delayed, bit for bit.
         * mutant: include/omxdsp/omx_idelay.h:107 `omx_lookahead_back(w, tgt, cap)` -> `omx_lookahead_back(w, tgt + 1u, cap)`
         * input: integer-pair
         * mutant: include/omxdsp/omx_idelay.h:120 `*cur = tgt;` -> ``
         * input: integer-pair */
        if (!(memcmp(&wl, &l[i], sizeof wl) == 0 || (wl == 0.0f && l[i] == 0.0f))) {
          FUZZ_SAY("steady delay %u: left sample %u is %g, the take says %g", (unsigned)tl, (unsigned)(done + i), (double)l[i], (double)wl);
          abort();
        }
      }
      else {
        /* A delay that moves on the left stays between the two taps it fades.
         * mutant: include/omxdsp/omx_idelay.h:117 `ring[r0] *` -> `2.0f * ring[r0] *`
         * input: integer-pair */
        if (!(l[i] >= fminf(wl, ol) - 1e-6f && l[i] <= fmaxf(wl, ol) + 1e-6f)) {
          FUZZ_SAY("fade %u -> %u: left sample %u is %g, outside %g and %g", (unsigned)from_l, (unsigned)tl, (unsigned)(done + i), (double)l[i], (double)ol, (double)wl);
          abort();
        }
      }
      if (!mono) {
        const float wr = take_at(taker, (long)(done + i) - (long)tr);
        const float orr = take_at(taker, (long)(done + i) - (long)from_r);
        if (steady_r) {
          /* A steady delay on the right is the take delayed, bit for bit.
           * mutant: include/omxdsp/omx_idelay.h:168 `omx_idelay_apply(r, n, d->ring_r, d->cap, &d->wpos_r, &d->cur_r, tgt_r);` -> `{ omx_idelay_apply(r, n, d->ring_r, d->cap, &d->wpos_r, &d->cur_r, tgt_r); r[n - 1] += 1.0f; }`
           * input: integer-right-steady */
          if (!(memcmp(&wr, &r[i], sizeof wr) == 0 || (wr == 0.0f && r[i] == 0.0f))) {
            FUZZ_SAY("steady delay %u: right sample %u is %g, the take says %g", (unsigned)tr, (unsigned)(done + i), (double)r[i], (double)wr);
            abort();
          }
        }
        else {
          /* A delay that moves on the right stays between the two taps it fades.
           * mutant: include/omxdsp/omx_idelay.h:168 `omx_idelay_apply(r, n, d->ring_r, d->cap, &d->wpos_r, &d->cur_r, tgt_r);` -> `{ omx_idelay_apply(r, n, d->ring_r, d->cap, &d->wpos_r, &d->cur_r, tgt_r); r[n - 1] += 1.0f; }`
           * input: integer-pair */
          if (!(r[i] >= fminf(wr, orr) - 1e-6f && r[i] <= fmaxf(wr, orr) + 1e-6f)) {
            FUZZ_SAY("fade %u -> %u: right sample %u is %g, outside %g and %g", (unsigned)from_r, (unsigned)tr, (unsigned)(done + i), (double)r[i], (double)orr, (double)wr);
            abort();
          }
        }
      }
    }
    last_l = tl;
    last_r = tr;
    done += n;
  }
  free(rl);
  free(rr);
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  struct fuzz_in in = fuzz_in(data, size);
  const uint8_t flags = fuzz_u8(&in);
  const uint32_t cap = 1u + fuzz_u16(&in) % RING_MAX;
  fuzz_ledger_reset();
  if (flags & 1u) fractional(&in, (flags & 8u) ? (int)(int8_t)fuzz_u8(&in) : (flags & 2u) ? 5 : 3, cap);
  else integer(&in, cap, (flags >> 2) & 1, (flags >> 4) & 1);
  fuzz_ledger_clean("delay");
  return 0;
}
