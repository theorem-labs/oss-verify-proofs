// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>

/* libFuzzer harness: the scalar laws every control port goes through before a kernel reads it:
 * omx_clampf / omx_clamp_or / omx_unit (omx_param.h), the dB and linear conversions
 * (omx_units.h), the pan, balance and fader laws, the ramp a block applies a changed value
 * through, the wet/dry mix and cross-fade, and the one-pole constructors (omx_onepole.h).
 *
 * Input: a sequence of calls, each a u8 selector and the words its call reads (raw floats: any
 * value a host, an atom or a knob can carry, NaN and the infinities included, wherever the
 * function's own contract takes any value, and finite or in-travel words where it states a PRE).
 * The sequence ends with the input.
 *
 * Properties, each an abort():
 *   - a clamp lands inside its travel, whatever the word (NaN included), and a word already inside
 *     is returned unchanged; omx_clamp_or turns a non-finite word into the declared default;
 *   - dB to linear is never negative and, inside +-150 dB, finite and positive, and linear to dB
 *     brings it back to 0.01 dB; linear to dB never leaves its floor and never goes non-finite;
 *   - the pan law is constant power, cos^2 + sin^2 = 1 (1e-5), on [-1, 1]; the balance law
 *     never boosts: both legs in [0, 1], at least one of them 1, any pan;
 *   - the fader law's coefficient is finite, never negative, and zero when the strip or the DCA
 *     is muted;
 *   - a ramp over n samples starts at the applied value (0 for a non-finite one), reaches no
 *     sample outside the span of its start and target, and ends on the target; nothing in it is
 *     non-finite whatever the caller held;
 *   - the wet/dry mix of finite samples lies between the dry and the wet one, and the
 *     cross-fade's every sample lies between the outgoing and the incoming body's;
 *   - the one-pole constructors give a pole in [0, 1) for any finite time or corner (the
 *     fix of omx-dsp#250), a rescaled pole stays in [0, 1], and one step of the filter lies between
 *     the input and the state.
 */
#define OMX_CONTRACT_STORAGE 1
#include <float.h>

#include <omxdsp/omx_balance_law.h>
#include <omxdsp/omx_fader_law.h>
#include <omxdsp/omx_onepole.h>
#include <omxdsp/omx_param.h>
#include <omxdsp/omx_ramp.h>
#include <omxdsp/omx_units.h>
#include <omxdsp/omx_wetdry.h>

#include "fuzz.h"

#define CALLS_MAX 64
#define BLOCK_MAX 64u

static int is_fin(float x) { return x - x == 0.0f; }

static float fin_or(float x, float d) { return is_fin(x) ? x : d; }

static void call_clamp(struct fuzz_in *in) {
  const float v = fuzz_f32(in);
  float lo = fin_or(fuzz_f32(in), -1.0f), hi = fin_or(fuzz_f32(in), 1.0f);
  if (lo > hi) {
    const float t = lo;
    lo = hi;
    hi = t;
  }
  const float c = omx_clampf(v, lo, hi);
  /* A clamp lands inside its travel, whatever the word.
   * mutant: include/omxdsp/omx_param.h:37 `(v <= hi ? v : hi)` -> `v`
   * input: clamp */
  if (!(c >= lo && c <= hi)) {
    FUZZ_SAY("omx_clampf(%g, %g, %g) = %g is outside its travel", (double)v, (double)lo, (double)hi, (double)c);
    abort();
  }
  if (v >= lo && v <= hi) {
    /* A word already inside the travel comes back unchanged.
     * mutant: include/omxdsp/omx_param.h:37 `(v <= hi ? v : hi)` -> `(v <= hi ? lo : hi)`
     * input: clamp */
    if (!(c == v)) {
      FUZZ_SAY("omx_clampf moved %g, which is inside [%g, %g]", (double)v, (double)lo, (double)hi);
      abort();
    }
  }
  float d = fin_or(fuzz_f32(in), lo);
  d = d < lo ? lo : d > hi ? hi : d;
  const float o = omx_clamp_or(v, lo, hi, d);
  /* omx_clamp_or lands inside the travel too.
   * mutant: include/omxdsp/omx_param.h:56 `omx_clampf(v, lo, hi)` -> `v`
   * input: clamp */
  if (!(o >= lo && o <= hi)) {
    FUZZ_SAY("omx_clamp_or(%g, %g, %g, %g) = %g is outside its travel", (double)v, (double)lo, (double)hi, (double)d, (double)o);
    abort();
  }
  if (!is_fin(v)) {
    /* A word that is not finite reads as the declared default.
     * mutant: include/omxdsp/omx_param.h:56 `: dflt` -> `: lo`
     * input: clamp */
    if (!(o == d)) {
      FUZZ_SAY("omx_clamp_or(%g) = %g is not the default %g", (double)v, (double)o, (double)d);
      abort();
    }
  }
  const float u = omx_unit(v);
  /* omx_unit lands in [0, 1].
   * mutant: include/omxdsp/omx_param.h:67 `omx_clampf(v, 0.0f, 1.0f)` -> `v`
   * input: clamp */
  if (!(u >= 0.0f && u <= 1.0f)) {
    FUZZ_SAY("omx_unit(%g) = %g", (double)v, (double)u);
    abort();
  }
}

static void call_units(struct fuzz_in *in) {
  const float db = fuzz_f32(in);
  const float g = omx_db_to_lin(fin_or(db, 0.0f));
  /* dB to linear is never negative.
   * mutant: include/omxdsp/omx_units.h:24 `powf(10.0f, db * 0.05f)` -> `-powf(10.0f, db * 0.05f)`
   * input: units */
  if (!(!(g < 0.0f))) {
    FUZZ_SAY("omx_db_to_lin(%g) = %g is negative", (double)db, (double)g);
    abort();
  }
  const float dbc = fin_or(db, 0.0f);
  if (dbc >= -150.0f && dbc <= 150.0f) {
    /* Inside +-150 dB, dB to linear is finite and above 0.
     * mutant: include/omxdsp/omx_units.h:24 `powf(10.0f, db * 0.05f)` -> `0.0f * powf(10.0f, db * 0.05f)`
     * input: units */
    if (!(is_fin(g) && g > 0.0f)) {
      FUZZ_SAY("omx_db_to_lin(%g) = %g is not finite and positive", (double)dbc, (double)g);
      abort();
    }
    const float back = omx_lin_to_db(g);
    /* Linear to dB brings a gain back to its dB, to 0.01 dB.
     * mutant: include/omxdsp/omx_units.h:36 `20.0f * log10f` -> `21.0f * log10f`
     * input: units */
    if (!(fabsf(back - dbc) <= 0.01f)) {
      FUZZ_SAY("dB %g -> linear %g -> dB %g", (double)dbc, (double)g, (double)back);
      abort();
    }
    const float gp = omx_db_to_lin_poly(dbc);
    /* The polynomial dB to linear is finite and above 0 inside +-150 dB.
     * mutant: include/omxdsp/omx_units.h:123 `p * scale` -> `p * scale * NAN`
     * input: units */
    if (!(is_fin(gp) && gp > 0.0f)) {
      FUZZ_SAY("omx_db_to_lin_poly(%g) = %g", (double)dbc, (double)gp);
      abort();
    }
  }
  const float lin = fuzz_f32(in);
  if (is_fin(lin)) { /* +Inf is +Inf dB: the floor is the law for what is small, not for what is not finite */
    const float l = omx_lin_to_db(lin);
    /* Linear to dB keeps its floor and stays finite for any finite word: 0 is the floor, not -Inf.
     * mutant: include/omxdsp/omx_units.h:36 `lin < floor_lin ? floor_lin : lin` -> `lin`
     * input: units */
    if (!(is_fin(l) && l >= OMX_LIN_TO_DB_FLOOR_DB - 0.001f)) {
      FUZZ_SAY("omx_lin_to_db(%g) = %g", (double)lin, (double)l);
      abort();
    }
  }
  if (is_fin(lin)) {
    const float p = omx_lin_to_db_poly(lin);
    /* The polynomial linear to dB is finite for any finite word.
     * mutant: include/omxdsp/omx_units.h:89 `8.685889638065037f` -> `NAN`
     * input: units */
    if (!(is_fin(p))) {
      FUZZ_SAY("omx_lin_to_db_poly(%g) = %g", (double)lin, (double)p);
      abort();
    }
  }
}

static void call_pan_fader(struct fuzz_in *in) {
  const float pan = fuzz_range(in, -1.0f, 1.0f);
  const float gl = omx_pan_law_gain(pan, OMX_PAN_LEG_L), gr = omx_pan_law_gain(pan, OMX_PAN_LEG_R);
  /* The pan law is constant power: the squares of the two legs add up to 1.
   * mutant: include/omxdsp/omx_fader_law.h:58 `sinf(theta)` -> `cosf(theta)`
   * input: pan-fader */
  if (!(fabsf(gl * gl + gr * gr - 1.0f) <= 1e-5f)) {
    FUZZ_SAY("the pan law at %g: %g^2 + %g^2 is not 1", (double)pan, (double)gl, (double)gr);
    abort();
  }
  const float any = fuzz_f32(in);
  float bl, br;
  omx_balance_law(any, &bl, &br);
  /* The balance law never boosts: both legs in [0, 1], and one of them is 1.
   * mutant: include/omxdsp/omx_balance_law.h:47 `1.0f - p` -> `1.0f + p`
   * input: pan-fader */
  if (!(bl >= 0.0f && bl <= 1.0f && br >= 0.0f && br <= 1.0f && (bl == 1.0f || br == 1.0f))) {
    FUZZ_SAY("the balance law at %g gives (%g, %g)", (double)any, (double)bl, (double)br);
    abort();
  }
  struct omx_fader_law_params p;
  p.fader_db = fuzz_range(in, -200.0f, 60.0f);
  p.pan = pan;
  p.pan_leg = (int)fuzz_below(in, 3);
  p.send_lin = fabsf(fin_or(fuzz_f32(in), 1.0f));
  if (p.send_lin > 1e6f) p.send_lin = 1e6f;
  p.mute = fuzz_u8(in) & 1;
  p.dca_lin = fabsf(fin_or(fuzz_f32(in), 1.0f));
  if (p.dca_lin > 1e6f) p.dca_lin = 1e6f;
  p.dca_mute = fuzz_u8(in) & 1;
  const float g = omx_fader_law_coeff(&p);
  /* The fader law's coefficient is finite and not negative.
   * mutant: include/omxdsp/omx_fader_law.h:85 `fader * pan` -> `-fader * pan`
   * input: pan-fader */
  if (!(is_fin(g) && g >= 0.0f)) {
    FUZZ_SAY("the fader law gives %g", (double)g);
    abort();
  }
  if (p.mute || p.dca_mute) {
    /* A muted strip or DCA has a coefficient of 0.
     * mutant: include/omxdsp/omx_fader_law.h:83 `p->mute ? 0.0f : 1.0f` -> `p->mute ? 1.0f : 1.0f`
     * input: pan-fader */
    if (!(g == 0.0f)) {
      FUZZ_SAY("a muted entry's coefficient is %g", (double)g);
      abort();
    }
  }
}

static void call_ramp(struct fuzz_in *in) {
  /* Any word, as far as a ramp's own arithmetic goes: a non-finite one reads as 0; past 1e30 the
   * difference of the two ends, and cur + step * i, leave a float, which no gain or level reaches. */
  float cur = fuzz_f32(in), tgt = fuzz_f32(in);
  if (is_fin(cur) && fabsf(cur) > 1e30f) cur = copysignf(1e30f, cur);
  if (is_fin(tgt) && fabsf(tgt) > 1e30f) tgt = copysignf(1e30f, tgt);
  const uint32_t n = 1u + fuzz_below(in, BLOCK_MAX);
  float held = cur;
  const struct omx_ramp r = omx_ramp_begin(&held, tgt, n);
  const float start = is_fin(cur) ? cur : 0.0f, end = is_fin(tgt) ? tgt : 0.0f;
  const float lo = fminf(start, end), hi = fmaxf(start, end);
  const float slack = 1e-5f * fmaxf(fabsf(lo), fabsf(hi)) + FLT_MIN; /* the rounding of cur + step*i, a denormal one included */
  /* A ramp starts at the applied value, 0 for one that is not finite.
   * mutant: include/omxdsp/omx_ramp.h:56 `r.cur + r.step` -> `r.tgt + r.step`
   * input: ramp */
  if (!(omx_ramp_at(r, 0) == start)) {
    FUZZ_SAY("a ramp from %g does not start there (%g)", (double)cur, (double)omx_ramp_at(r, 0));
    abort();
  }
  for (uint32_t i = 0; i < n; i++) {
    const float x = omx_ramp_at(r, i);
    /* No sample of a ramp leaves the span of its two ends.
     * mutant: include/omxdsp/omx_ramp.h:56 `r.step * (float)i` -> `2.0f * r.step * (float)i`
     * input: ramp */
    if (!(is_fin(x) && x >= lo - slack && x <= hi + slack)) {
      FUZZ_SAY("ramp %g -> %g over %u: sample %u is %g", (double)cur, (double)tgt, (unsigned)n, (unsigned)i, (double)x);
      abort();
    }
  }
  omx_ramp_end(r, &held);
  /* A ramp ends on its target.
   * mutant: include/omxdsp/omx_ramp.h:65 `*cur = r.tgt` -> `*cur = r.cur`
   * input: ramp */
  if (!(held == end)) {
    FUZZ_SAY("a ramp ends on %g, not %g", (double)held, (double)end);
    abort();
  }
}

static void call_wetdry(struct fuzz_in *in) {
  const float mix = fuzz_range(in, 0.0f, 1.0f), dry = 1.0f - mix;
  const float xl = fuzz_range(in, -8.0f, 8.0f), xr = fuzz_range(in, -8.0f, 8.0f);
  const float wl = fuzz_range(in, -8.0f, 8.0f), wr = fuzz_range(in, -8.0f, 8.0f);
  float l, r;
  omx_wetdry_mix(&l, &r, xl, xr, wl, wr, dry, mix);
  const float tol = 1e-5f;
  /* A wet/dry mix of finite samples lies between the dry one and the wet one.
   * mutant: include/omxdsp/omx_wetdry.h:35 `dry * xl` -> `2.0f * dry * xl`
   * input: wetdry */
  if (!(l >= fminf(xl, wl) - tol && l <= fmaxf(xl, wl) + tol && r >= fminf(xr, wr) - tol && r <= fmaxf(xr, wr) + tol)) {
    FUZZ_SAY("the wet/dry mix at %g is outside its two inputs", (double)mix);
    abort();
  }
  float a[BLOCK_MAX], b[BLOCK_MAX], d[BLOCK_MAX];
  const uint32_t n = 1u + fuzz_below(in, BLOCK_MAX);
  for (uint32_t i = 0; i < n; i++) {
    a[i] = fuzz_range(in, -4.0f, 4.0f);
    b[i] = fuzz_range(in, -4.0f, 4.0f);
  }
  omx_wetdry_xfade_block(d, a, b, n);
  for (uint32_t i = 0; i < n; i++)
    /* Each sample of a cross-fade lies between the two bodies.
     * mutant: include/omxdsp/omx_wetdry.h:79 `(step * (float)i)` -> `(2.0f * step * (float)i)`
     * input: wetdry */
    if (!(d[i] >= fminf(a[i], b[i]) - tol && d[i] <= fmaxf(a[i], b[i]) + tol)) {
      FUZZ_SAY("the cross-fade's sample %u (%g) is outside %g and %g", (unsigned)i, (double)d[i], (double)a[i], (double)b[i]);
      abort();
    }
}

static void call_onepole(struct fuzz_in *in) {
  const float sr = OMX_DECLARED_RATES[fuzz_below(in, OMX_DECLARED_RATE_COUNT)];
  const float ms = fin_or(fuzz_f32(in), 0.0f), hz = fin_or(fuzz_f32(in), 0.0f);
  const float pt = omx_pole_from_time_ms(ms, sr), pc = omx_pole_from_cutoff_hz(hz, sr);
  /* A time constant gives a pole in [0, 1), however long the time.
   * mutant: include/omxdsp/omx_onepole.h:119 `fminf(expf(-1.0f / (ms * 0.001f * sr)), OMX_POLE_MAX)` -> `expf(-1.0f / (ms * 0.001f * sr))`
   * input: onepole */
  if (!(pt >= 0.0f && pt < 1.0f)) {
    FUZZ_SAY("omx_pole_from_time_ms(%g, %g) = %g", (double)ms, (double)sr, (double)pt);
    abort();
  }
  /* A corner gives a pole in [0, 1), however low the corner.
   * mutant: include/omxdsp/omx_onepole.h:138 `fminf(expf(-2.0f * (float)M_PI * hz / sr), OMX_POLE_MAX)` -> `expf(-2.0f * (float)M_PI * hz / sr)`
   * input: onepole */
  if (!(pc >= 0.0f && pc < 1.0f)) {
    FUZZ_SAY("omx_pole_from_cutoff_hz(%g, %g) = %g", (double)hz, (double)sr, (double)pc);
    abort();
  }
  const float p = fuzz_range(in, 0.0f, 1.0f), ref = fuzz_f32(in), run = fuzz_f32(in);
  const float q = omx_pole_rescale(p, ref, run);
  /* A rescaled pole stays in [0, 1].
   * mutant: include/omxdsp/omx_onepole.h:163 `powf(p, ref / sr)` -> `2.0f`
   * input: onepole */
  if (!(q >= 0.0f && q <= 1.0f)) {
    FUZZ_SAY("omx_pole_rescale(%g, %g, %g) = %g", (double)p, (double)ref, (double)run, (double)q);
    abort();
  }
  float s = fuzz_range(in, -4.0f, 4.0f);
  const float x = fuzz_range(in, -4.0f, 4.0f), s0 = s;
  const float y = omx_onepole(&s, x, pt);
  /* One step of the filter lies between the input and the state, and the state is what it returns.
   * mutant: include/omxdsp/omx_onepole.h:51 `x * (1.0f - pole)` -> `2.0f * x * (1.0f - pole)`
   * input: onepole */
  if (!(y >= fminf(x, s0) - 1e-5f && y <= fmaxf(x, s0) + 1e-5f && y == s)) {
    FUZZ_SAY("a one-pole step from %g toward %g at pole %g gave %g", (double)s0, (double)x, (double)pt, (double)y);
    abort();
  }
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  struct fuzz_in in = fuzz_in(data, size);
  fuzz_ledger_reset();
  for (int i = 0; i < CALLS_MAX && in.n > 0; i++) {
    switch (fuzz_below(&in, 6)) {
      case 0: call_clamp(&in); break;
      case 1: call_units(&in); break;
      case 2: call_pan_fader(&in); break;
      case 3: call_ramp(&in); break;
      case 4: call_wetdry(&in); break;
      default: call_onepole(&in); break;
    }
    fuzz_ledger_clean("laws");
  }
  return 0;
}
