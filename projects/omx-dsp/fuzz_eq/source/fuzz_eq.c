// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>

/* libFuzzer harness: the EQ's design and run path (omx_eq_design.h, omx_biquad.h,
 * omx_magnitude.h): a bank of bands designed at a rate from engineering values, the head
 * pass filters, then a block through the cascade and the bank's magnitude.
 *
 * Input:  [0]     bit 0: the rate is any rate from 8 to 768 kHz (u16 over that span), else one
 *                 of the nine of the oracle grid; bit 1: the EQ is on; bit 2: the run is
 *                 stereo, else one leg
 *         [1..]   the rate (one byte or two), the head filters (on, slope, corner as a raw
 *                 double each), the band count (1..OMX_EQ_MAX_BANDS), each band's kind, switch,
 *                 corner (a raw double), Q (a raw double) and gain (a u16 over +-24 dB), then a
 *                 u8 block length (1..255) and the block's samples (fuzz_block, finite).
 *
 * The corner and the Q are ANY finite double, a negative or an astronomical one included (the
 * design clamps the corner into [1 Hz, 0.999 Nyquist] and reads a Q at or below 0 as 1e-3); a
 * non-finite one is not in the design's contract and is read as 1 kHz and Q 1.
 *
 * Properties, each an abort():
 *   - no contract the library states is broken (the ledger stays empty): every section the bank
 *     designs has finite coefficients and both poles inside the unit circle;
 *   - the same sections are stable as the harness computes it from the coefficients, and the bank has at most as many sections as bands (a band that is off is
 *     not in it);
 *   - section i belongs to the i-th band that is on: its gain at DC is the one omx_eq_design.h
 *     gives that band's kind and gain, to a tolerance, and it is parked exactly when the harness's
 *     own rule finds a peaking or shelf band at 0 dB;
 *   - the cascade, over finite samples, gives finite samples on both legs, and a bank with no live
 *     section leaves the block as it was, bit for bit, on each leg it runs;
 *   - the bank's magnitude (dB) is finite at any frequency, and a bank with no live section is
 *     0 dB there;
 *   - the head filters make at most OMX_EQ_PASS_MAX_SECTIONS sections, each stable;
 *   - the width-to-Q conversions give a finite Q (0 where the width overflows sinh, as the committed table
 *     has it; positive for the octaves law) for any finite width above 0.
 */
#define OMX_CONTRACT_STORAGE 1
#include "fuzz.h"

#include <omxdsp/omx_biquad.h>
#include <omxdsp/omx_eq_design.h>
#include <omxdsp/omx_magnitude.h>


#define BLOCK_MAX 255u

static double fin_or(double x, double d) { return isfinite(x) ? x : d; }

/* Both poles of {b0, b1, b2, a1, a2} inside the unit circle: the Jury conditions, the harness's own. */
static int stable(const double *c) { return fabs(c[3]) < 1.0 + c[4] && c[4] < 1.0; }

/* The band behind section i: the i-th one that is on. The caller has checked there are that many. */
static const struct omx_eq_band *band_of(const struct omx_eq_band *bands, uint32_t i) {
  while (!bands->on || i-- != 0u) bands++;
  return bands;
}

/* A band that runs as the identity: a peaking or shelf band at exactly 0 dB. */
static int parked(const struct omx_eq_band *b) {
  return (b->kind == OMX_EQ_PEAKING || b->kind == OMX_EQ_LOWSHELF || b->kind == OMX_EQ_HIGHSHELF) && b->gain_db == 0.0;
}

/* A section's gain at DC by its band, as the comments of omx_eq_design.h give it: a low shelf
 * 10^(gain/20), a high-pass and a band-pass none, and every other kind unity. */
static double dc_gain(const struct omx_eq_band *b) {
  if (b->kind == OMX_EQ_LOWSHELF) return pow(10.0, b->gain_db / 20.0);
  return b->kind == OMX_EQ_HIGHPASS || b->kind == OMX_EQ_BANDPASS ? 0.0 : 1.0;
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  struct fuzz_in in = fuzz_in(data, size);
  const uint8_t flags = fuzz_u8(&in);
  const double rate = (double)((flags & 1u) ? fuzz_range(&in, 8000.0f, 768000.0f) : fuzz_rate(&in));
  fuzz_rate_undeclared = !omx_rate_is_declared((float)rate);
  fuzz_ledger_reset();

  /* a braced initialiser reads its words in no fixed order: each field is its own statement */
  struct omx_eq_pass hpf, lpf;
  hpf.on = fuzz_u8(&in) & 1;
  hpf.freq_hz = fin_or(fuzz_f64(&in), 1000.0);
  hpf.slope_24 = fuzz_u8(&in) & 1;
  lpf.on = fuzz_u8(&in) & 1;
  lpf.freq_hz = fin_or(fuzz_f64(&in), 1000.0);
  lpf.slope_24 = fuzz_u8(&in) & 1;
  double pass[OMX_EQ_PASS_MAX_SECTIONS][5];
  const uint32_t np = omx_eq_pass_design(&hpf, &lpf, rate, pass);
  /* The head filters write at most their limit of sections.
   * mutant: include/omxdsp/omx_eq_design.h:528 `return n;` -> `return n + 9u;`
   * input: bank-0 */
  if (!(np <= OMX_EQ_PASS_MAX_SECTIONS)) {
    FUZZ_SAY("the head filters wrote %u sections", (unsigned)np);
    abort();
  }
  for (uint32_t i = 0; i < np; i++)
    /* Each section of the head filters is stable and finite, by the harness's own reading of its coefficients.
     * mutant: include/omxdsp/omx_eq_design.h:525 `coeffs[n++]);` -> `coeffs[n++]), coeffs[n - 1][4] = 2.0;`
     * input: bank-0 */
    if (!(stable(pass[i]) && isfinite(pass[i][0]) && isfinite(pass[i][1]) && isfinite(pass[i][2]))) {
      FUZZ_SAY("head section %u is unstable or not finite", (unsigned)i);
      abort();
    }
  fuzz_ledger_check("eq pass", omx_rate_is_declared((float)rate), 0);

  const uint32_t nb = 1u + fuzz_below(&in, OMX_EQ_MAX_BANDS);
  struct omx_eq_band bands[OMX_EQ_MAX_BANDS];
  uint32_t on_count = 0;
  for (uint32_t i = 0; i < nb; i++) {
    bands[i].kind = (enum omx_eq_kind)fuzz_below(&in, OMX_EQ_ALLPASS2 + 1);
    bands[i].on = fuzz_u8(&in) & 1;
    bands[i].freq_hz = fin_or(fuzz_f64(&in), 1000.0);
    bands[i].q = fin_or(fuzz_f64(&in), 1.0);
    bands[i].gain_db = (double)fuzz_range(&in, -24.0f, 24.0f);
    if (fuzz_u8(&in) & 1) bands[i].gain_db = 0.0; /* a parked band is a case of its own */
    on_count += (uint32_t)bands[i].on;
  }
  double dcoef[OMX_EQ_MAX_BANDS][5];
  uint8_t enabled[OMX_EQ_MAX_BANDS];
  const uint32_t ns = omx_eq_bank_design((flags >> 1) & 1, bands, nb, rate, dcoef, enabled);
  /* The bank has at most as many sections as bands.
   * mutant: include/omxdsp/omx_eq_design.h:493 `return n;` -> `return nbands + 1u;`
   * input: bank-0 */
  if (!(ns <= nb)) {
    FUZZ_SAY("the bank has %u sections for %u bands", (unsigned)ns, (unsigned)nb);
    abort();
  }
  /* The bank has a section for each band that is on, and none with the EQ off.
   * mutant: include/omxdsp/omx_eq_design.h:487 `if (!b->on) continue;` -> ``
   * input: bank-off-band */
  if (!(((flags >> 1) & 1) ? ns == on_count : ns == 0)) {
    FUZZ_SAY("the bank has %u sections for %u bands that are on", (unsigned)ns, (unsigned)on_count);
    abort();
  }
  float coef[OMX_EQ_MAX_BANDS][5];
  uint32_t live = 0;
  for (uint32_t i = 0; i < ns; i++) {
    /* Each section of the bank is stable, by the harness's own reading of its coefficients.
     * mutant: include/omxdsp/omx_eq_design.h:488 `coeffs[n]);` -> `coeffs[n]), coeffs[n][4] = 2.0;`
     * input: bank-0 */
    if (!(stable(dcoef[i]))) {
      FUZZ_SAY("section %u is not stable: %g %g %g %g %g", (unsigned)i, dcoef[i][0], dcoef[i][1], dcoef[i][2], dcoef[i][3], dcoef[i][4]);
      abort();
    }
    for (int k = 0; k < 5; k++) {
      /* Each coefficient of the bank is finite.
       * mutant: include/omxdsp/omx_eq_design.h:488 `coeffs[n]);` -> `coeffs[n]), coeffs[n][0] = NAN;`
       * input: bank-0 */
      if (!(isfinite(dcoef[i][k]))) {
        FUZZ_SAY("section %u coefficient %d is not finite", (unsigned)i, k);
        abort();
      }
      coef[i][k] = (float)dcoef[i][k];
    }
    const struct omx_eq_band *own = band_of(bands, i);
    /* A section is parked exactly when its band is a peaking or shelf band at 0 dB.
     * mutant: include/omxdsp/omx_eq_design.h:489 `? 0u : 1u` -> `? 1u : 1u`
     * input: parked-and-live */
    if (!(enabled[i] == (parked(own) ? 0u : 1u))) {
      FUZZ_SAY("section %u has enabled %u, band kind %d at %g dB", (unsigned)i, (unsigned)enabled[i], (int)own->kind, own->gain_db);
      abort();
    }
    live += parked(own) ? 0u : 1u;
    const double dc_num = dcoef[i][0] + dcoef[i][1] + dcoef[i][2], dc_den = 1.0 + dcoef[i][3] + dcoef[i][4];
    /* A section has the gain at DC of the i-th band that is on. The denominator is positive in a
     * stable section; the tolerance leaves room for its rounding at the lowest corner (about 1e-5).
     * mutant: include/omxdsp/omx_eq_design.h:488 `b->kind, b->freq_hz, b->q, b->gain_db` -> `bands->kind, bands->freq_hz, bands->q, bands->gain_db`
     * input: shelf-then-shelf */
    if (!(fabs(dc_num - dc_gain(own) * dc_den) <= 1e-3 * fmax(dc_gain(own), 1.0) * dc_den)) {
      FUZZ_SAY("section %u has %g at DC, band kind %d at %g dB owes %g", (unsigned)i, dc_num / dc_den, (int)own->kind, own->gain_db, dc_gain(own));
      abort();
    }
  }
  fuzz_ledger_check("eq bank", omx_rate_is_declared((float)rate), 0);

  /* the magnitude of the bank: finite at any frequency, and 0 dB with nothing live */
  double f[4] = {fin_or(fuzz_f64(&in), 1000.0), 20.0, 1000.0, rate * 0.5}, db[4];
  omx_biquad_cascade_magnitude_db_d(dcoef, enabled, ns, f, 4, rate, -120.0, db);
  for (int i = 0; i < 4; i++) {
    /* The bank's magnitude is finite at any frequency.
     * mutant: include/omxdsp/omx_magnitude.h:125 `db_out[i] = db;` -> `db_out[i] = NAN;`
     * input: bank-0 */
    if (!(isfinite(db[i]))) {
      FUZZ_SAY("the bank's magnitude at %g Hz is %g", f[i], db[i]);
      abort();
    }
    if (live == 0) {
      /* A bank with no live section is 0 dB.
       * mutant: include/omxdsp/omx_magnitude.h:121 `double db = 0.0;` -> `double db = 1.0;`
       * input: bank-3 */
      if (!(db[i] == 0.0)) {
        FUZZ_SAY("a bank with no live section is %g dB at %g Hz", db[i], f[i]);
        abort();
      }
    }
  }
  fuzz_ledger_check("eq magnitude", omx_rate_is_declared((float)rate), 0);

  /* the cascade over a finite block */
  const uint32_t n = 1u + fuzz_below(&in, BLOCK_MAX);
  float l[BLOCK_MAX], r[BLOCK_MAX], l0[BLOCK_MAX], r0[BLOCK_MAX];
  fuzz_block(&in, l, n, 0);
  fuzz_block(&in, r, n, 0);
  memcpy(l0, l, n * sizeof(float));
  memcpy(r0, r, n * sizeof(float));
  float sl[OMX_EQ_MAX_BANDS][4], sr[OMX_EQ_MAX_BANDS][4];
  memset(sl, 0, sizeof sl);
  memset(sr, 0, sizeof sr);
  if ((flags >> 2) & 1) omx_biquad_cascade_stereo(l, r, n, ns, coef, enabled, sl, sr);
  else omx_biquad_cascade(l, n, ns, coef, enabled, sl);
  /* The cascade gives finite samples for finite samples.
   * mutant: include/omxdsp/omx_biquad.h:191 `enabled, state, NULL);` -> `enabled, state, NULL); buf[0] = NAN;`
   * input: bank-2 */
  if (!(fuzz_all_finite(l, n) && fuzz_all_finite(r, n))) {
    FUZZ_SAY("the cascade gave a non-finite sample");
    abort();
  }
  if (live == 0) {
    /* A bank with no live section leaves the block as it was, bit for bit.
     * mutant: include/omxdsp/omx_biquad.h:191 `enabled, state, NULL);` -> `enabled, state, NULL); buf[0] = 0.5f;`
     * input: eq-off-mono */
    if (!(memcmp(l, l0, n * sizeof(float)) == 0)) {
      FUZZ_SAY("a bank with no live section changed the block");
      abort();
    }
    /* In a stereo run, a bank with no live section leaves the right leg as it was too.
     * mutant: include/omxdsp/omx_biquad.h:166 `OMX_POST(!r ||` -> `if (r && !nl) r[0] = 0.5f; OMX_POST(!r ||`
     * input: bank-3 */
    if (!(!((flags >> 2) & 1) || memcmp(r, r0, n * sizeof(float)) == 0)) {
      FUZZ_SAY("a bank with no live section changed the right leg");
      abort();
    }
  }
  fuzz_ledger_check("eq cascade", omx_rate_is_declared((float)rate), 0);

  /* the width conversions */
  const double bw = fin_or(fuzz_f64(&in), 1.0);
  if (bw > 0.0) {
    const double q = omx_eq_bandwidth_q(fin_or(fuzz_f64(&in), 1000.0), bw, rate);
    /* The width to Q conversion is finite and not negative.
     * mutant: include/omxdsp/omx_eq_design.h:321 `1.0 / (2.0 *` -> `-1.0 / (2.0 *`
     * input: bank-0 */
    if (!(isfinite(q) && q >= 0.0)) {
      FUZZ_SAY("omx_eq_bandwidth_q gave %g", q);
      abort();
    } /* 0 where sinh overflows: the table has it */
  }
  const double q2 = omx_eq_octaves_q(bw);
  /* The octaves to Q conversion is finite and above 0.
   * mutant: include/omxdsp/omx_eq_design.h:417 `if (q < OMX_EQ_Q_MIN) q = OMX_EQ_Q_MIN;` -> `q = -q;`
   * input: bank-0 */
  if (!(isfinite(q2) && q2 > 0.0)) {
    FUZZ_SAY("omx_eq_octaves_q(%g) gave %g", bw, q2);
    abort();
  }
  fuzz_ledger_check("eq widths", omx_rate_is_declared((float)rate), 0);
  return 0;
}
