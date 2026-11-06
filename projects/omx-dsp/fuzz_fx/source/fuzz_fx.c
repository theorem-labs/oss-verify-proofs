// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>

/* libFuzzer harness: the instance faces of every effect (include/omxdsp/fx/omx_*_instance.h),
 * the code a host's audio callback runs: init at a rate, resolve the control ports, run a block.
 *
 * Input:  [0]     which effect (modulo the table below)
 *         [1]     bit 0: the rate is any rate from 8 to 768 kHz (u16 over that span, so
 *                 22050 and 11025 are as reachable as 48000: the faces refuse what is off the
 *                 oracle grid) rather than one of the nine the grid lists; bit 1: the blocks
 *                 are HOSTILE (any float word per sample); bits 2..4: a finite block's
 *                 loudness (fuzz_block)
 *         [2..]   the rate's two bytes (when bit 0 of [1] is set, else one byte picking from the
 *                 grid), then steps until the input ends or eight have run: a u8 whose bit 0 is
 *                 bypass, the effect's control ports in resolve's order (each a raw float or
 *                 int word: any value a host can put on a port), a u16 block length (1..512
 *                 frames, modulo) and the two channels' samples (fuzz_block).
 *
 * Two instances of the effect take the same calls: A runs each block IN PLACE (out == in, the
 * aliasing every face documents as safe), B copies it out of place.
 *
 * Properties, each an abort():
 *   - a refused init (a rate off the grid) leaves run() the identity, bit for bit, whatever
 *     the ports say;
 *   - no contract the library states is broken, on any port value or block (the ledger of
 *     omx_contract.h stays empty);
 *   - an instance that took finite samples gives finite samples back, at every port value;
 *   - ALIASING IS SAFE: A's in-place output equals B's out-of-place output, bit for bit;
 */
#define OMX_CONTRACT_STORAGE 1
#include "fuzz.h"

#include <omxdsp/fx/omx_chorus_instance.h>
#include <omxdsp/fx/omx_comp_instance.h>
#include <omxdsp/fx/omx_deesser_instance.h>
#include <omxdsp/fx/omx_delay_instance.h>
#include <omxdsp/fx/omx_doubler_instance.h>
#include <omxdsp/fx/omx_drive_instance.h>
#include <omxdsp/fx/omx_dyneq_instance.h>
#include <omxdsp/fx/omx_eq_instance.h>
#include <omxdsp/fx/omx_flanger_instance.h>
#include <omxdsp/fx/omx_gate_instance.h>
#include <omxdsp/fx/omx_geq_instance.h>
#include <omxdsp/fx/omx_leveler_instance.h>
#include <omxdsp/fx/omx_limiter_instance.h>
#include <omxdsp/fx/omx_mbcomp_instance.h>
#include <omxdsp/fx/omx_phaser_instance.h>
#include <omxdsp/fx/omx_pitch_instance.h>
#include <omxdsp/fx/omx_plosive_instance.h>
#include <omxdsp/fx/omx_reverb_instance.h>
#include <omxdsp/fx/omx_rotary_instance.h>
#include <omxdsp/fx/omx_suboct_instance.h>
#include <omxdsp/fx/omx_tone_instance.h>
#include <omxdsp/fx/omx_transient_instance.h>
#include <omxdsp/fx/omx_tremolo_instance.h>
#include <omxdsp/fx/omx_trim_instance.h>
#include <omxdsp/fx/omx_width_instance.h>


#define BLOCK_MAX 512u
#define STEPS_MAX 8

/* The ports of one resolve, read off the cursor `c`; the loop hands each instance its own copy, so
 * both see the same words. */
#define F() fuzz_f32(c)
#define I() fuzz_int(c)

struct fx {
  const char *name;
  size_t size;
  int (*init)(void *, float);
  void (*resolve)(void *, int bypass, struct fuzz_in *c);
  void (*run)(void *, const float *il, const float *ir, float *ol, float *or_, uint32_t n);
};

/* One effect: its type, init, the resolve body (reading ports with F() and I() from `c`) and the
 * run call. `bypass` is the first port of every face. */
#define FX_RUN_STD(prefix, T) \
  static void prefix##_run(void *s, const float *il, const float *ir, float *ol, float *or_, uint32_t n) { \
    omx_##prefix##_instance_run((T *)s, il, ir, ol, or_, n); \
  }
#define FX_INIT_STD(prefix, T) \
  static int prefix##_init(void *s, float sr) { return omx_##prefix##_instance_init((T *)s, sr); }
#define FX_STD(prefix, T, ...) \
  FX_INIT_STD(prefix, T) \
  FX_RUN_STD(prefix, T) \
  static void prefix##_resolve(void *s_, int bypass, struct fuzz_in *c) { \
    T *s = (T *)s_; \
    (void)c; \
    __VA_ARGS__ \
  }

FX_STD(chorus, OmxChorusInstance,
       { float spread = F(), rate = F(), depth = F(), voices = F(), mix = F();
         omx_chorus_instance_resolve(s, bypass, spread, rate, depth, voices, mix); })
FX_STD(deesser, OmxDeesserInstance,
       { float f = F(), w = F(), th = F(), ra = F(), rg = F(), at = F(), re = F();
         int mode = I();
         omx_deesser_instance_resolve(s, bypass, f, w, th, ra, rg, at, re, mode); })
FX_STD(delay, OmxDelayInstance,
       { float t = F(), fb = F(), tone = F(), mix = F();
         int pp = I(), sync = I(), div = I(), mode = I();
         float dd = F(), dt = F(), dr = F();
         omx_delay_instance_set_tempo(s, F());
         omx_delay_instance_resolve(s, bypass, t, fb, tone, mix, pp, sync, div, mode, dd, dt, dr); })
FX_STD(doubler, OmxDoublerInstance,
       { float v = F(), d = F(), dc = F(), mr = F(), md = F(), sp = F(), mx = F();
         omx_doubler_instance_resolve(s, bypass, v, d, dc, mr, md, sp, mx); })
FX_STD(drive, OmxDriveInstance,
       { float am = F(), ch = F(), bf = F(), mx = F(), tr = F();
         int cu = I(), ba = I(), ag = I(), sl = I(), hf = I(), os = I();
         omx_drive_instance_resolve(s, bypass, am, ch, bf, mx, tr, cu, ba, ag, sl, hf, os); })
FX_STD(flanger, OmxFlangerInstance,
       { float r = F(), d = F(), fb = F(), m = F(); omx_flanger_instance_resolve(s, bypass, r, d, fb, m); })
FX_STD(leveler, OmxLevelerInstance,
       { float a = F(); int d = I(), sp = I(); omx_leveler_instance_resolve(s, bypass, a, d, sp); })
FX_STD(limiter, OmxLimiterInstance,
       { float ce = F(), la = F(), re = F(); omx_limiter_instance_resolve(s, bypass, ce, la, re); })
FX_STD(phaser, OmxPhaserInstance,
       { float r = F(), b = F(), d = F(), st = F(), fb = F(), m = F();
         omx_phaser_instance_resolve(s, bypass, r, b, d, st, fb, m); })
FX_STD(pitch, OmxPitchInstance,
       { float se = F(), ce = F(), m = F(); omx_pitch_instance_resolve(s, bypass, se, ce, m); })
FX_STD(plosive, OmxPlosiveInstance,
       { float a = F(), b = F(), cc = F(), d = F(), e = F(), f = F(), g = F(), h = F(), i = F();
         omx_plosive_instance_resolve(s, bypass, a, b, cc, d, e, f, g, h, i); })
FX_STD(reverb, OmxReverbInstance,
       { float pm = F(), mix = F(), size = F(), damp = F(), width = F(), pre = F(), lc = F(), hc = F();
         float rev = F(), hold = F(), rel = F(), gt = F();
         int alg = I();
         float ed = F(), td = F(), es = F(), dd = F(), dth = F(), dr = F();
         int wd = I();
         float df = F(), dt = F();
         omx_reverb_instance_resolve(s, bypass, pm, mix, size, damp, width, pre, lc, hc, rev, hold, rel, gt, alg,
                                     ed, td, es, dd, dth, dr, wd, df, dt); })
FX_STD(rotary, OmxRotaryInstance,
       { float a = F(), b = F(), cc = F(), d = F(), e = F(), f = F(), g = F(); int sp = I();
         omx_rotary_instance_resolve(s, bypass, a, b, cc, d, e, f, g, sp); })
FX_STD(suboct, OmxSuboctInstance,
       { int r = I(); float o1 = F(), o2 = F(), dry = F(), tg = F();
         omx_suboct_instance_resolve(s, bypass, r, o1, o2, dry, tg); })
FX_STD(tone, OmxToneInstance,
       { float a = F(), b = F(), cc = F(), d = F(); omx_tone_instance_resolve(s, bypass, a, b, cc, d); })
FX_STD(transient, OmxTransientInstance,
       { float a = F(), b = F(), cc = F(), d = F(), e = F(); omx_transient_instance_resolve(s, bypass, a, b, cc, d, e); })
FX_STD(tremolo, OmxTremoloInstance,
       { float r = F(), d = F(), m = F(); int mode = I(); omx_tremolo_instance_resolve(s, bypass, r, d, m, mode); })
FX_STD(trim, OmxTrimInstance, { omx_trim_instance_resolve(s, bypass, F()); })
FX_STD(width, OmxWidthInstance,
       { float w = F(); int ps = I(); float pm = F(); int bm = I(); float bh = F();
         omx_width_instance_resolve(s, bypass, w, ps, pm, bm, bh); })

/* The faces with array ports, and the two with a key or a double rate. */
FX_INIT_STD(comp, OmxCompInstance)
FX_RUN_STD(comp, OmxCompInstance)
static void comp_resolve(void *s_, int bypass, struct fuzz_in *c) {
  OmxCompInstance *s = (OmxCompInstance *)s_;
  float th = F(), ra = F(), kn = F(), at = F(), re = F(), mk = F(), mx = F();
  int kind = I(), dov = I(), dtop = I(), ks = I();
  float khp = F(), klp = F(), kt = F();
  int kl = I();
  float ho = F();
  int dl = I(), du = I();
  float rg = F();
  int rm = I();
  omx_comp_instance_resolve(s, bypass, th, ra, kn, at, re, mk, mx, kind, dov, dtop, ks, khp, klp, kt, kl, ho, dl, du,
                            rg, rm);
}

FX_INIT_STD(gate, OmxGateInstance)
static void gate_run(void *s, const float *il, const float *ir, float *ol, float *or_, uint32_t n) {
  omx_gate_instance_run((OmxGateInstance *)s, il, il, ir, ol, or_, n);
}
static void gate_resolve(void *s_, int bypass, struct fuzz_in *c) {
  OmxGateInstance *s = (OmxGateInstance *)s_;
  int ks = I();
  float th = F(), rg = F(), k0 = F(), k1 = F(), at = F(), ho = F(), re = F(), hy = F(), ra = F(), hp = F(),
        lp = F();
  int kl = I();
  float kt = F();
  omx_gate_instance_resolve(s, bypass, ks, th, rg, k0, k1, at, ho, re, hy, ra, hp, lp, kl, kt);
}

FX_RUN_STD(dyneq, OmxDyneqInstance)
FX_INIT_STD(dyneq, OmxDyneqInstance)
static void dyneq_resolve(void *s_, int bypass, struct fuzz_in *c) {
  OmxDyneqInstance *s = (OmxDyneqInstance *)s_;
  enum { N = OMX_DYNEQ_INSTANCE_BANDS };
  int on[N], ty[N], dm[N], li[N];
  float fr[N], ga[N], q[N], th[N], ra[N], rg[N], at[N], re[N];
  for (int i = 0; i < N; i++) {
    on[i] = I(); ty[i] = I(); dm[i] = I(); li[i] = I();
    fr[i] = F(); ga[i] = F(); q[i] = F(); th[i] = F(); ra[i] = F(); rg[i] = F(); at[i] = F(); re[i] = F();
  }
  omx_dyneq_instance_resolve(s, bypass, on, ty, fr, ga, q, dm, th, ra, rg, at, re, li, F());
}

FX_RUN_STD(eq, OmxEqInstance)
FX_INIT_STD(eq, OmxEqInstance)
static void eq_resolve(void *s_, int bypass, struct fuzz_in *c) {
  OmxEqInstance *s = (OmxEqInstance *)s_;
  enum { N = OMX_EQ_INSTANCE_BANDS };
  int hon = I(), hsl = I(), lon = I(), lsl = I();
  float hf = F(), lf = F();
  int ty[N], on[N];
  float fr[N], ga[N], q[N];
  for (int i = 0; i < N; i++) { ty[i] = I(); on[i] = I(); fr[i] = F(); ga[i] = F(); q[i] = F(); }
  omx_eq_instance_resolve(s, bypass, hon, hf, hsl, lon, lf, lsl, ty, fr, ga, q, on);
}

FX_RUN_STD(geq, OmxGeqInstance)
static int geq_init(void *s, float sr) { return omx_geq_instance_init((OmxGeqInstance *)s, (double)sr); }
static void geq_resolve(void *s_, int bypass, struct fuzz_in *c) {
  float band[OMX_GEQ_BANDS];
  for (int i = 0; i < OMX_GEQ_BANDS; i++) band[i] = F();
  omx_geq_instance_resolve((OmxGeqInstance *)s_, bypass, band);
}

FX_RUN_STD(mbcomp, OmxMbcompInstance)
FX_INIT_STD(mbcomp, OmxMbcompInstance)
static void mbcomp_resolve(void *s_, int bypass, struct fuzz_in *c) {
  OmxMbcompInstance *s = (OmxMbcompInstance *)s_;
  float bands = F(), xo[OMX_MBC_MAX_XOVERS];
  float th[OMX_MBC_MAX_BANDS], ra[OMX_MBC_MAX_BANDS], at[OMX_MBC_MAX_BANDS], re[OMX_MBC_MAX_BANDS],
      mk[OMX_MBC_MAX_BANDS];
  int so[OMX_MBC_MAX_BANDS], bb[OMX_MBC_MAX_BANDS];
  for (int i = 0; i < OMX_MBC_MAX_XOVERS; i++) xo[i] = F();
  for (int i = 0; i < OMX_MBC_MAX_BANDS; i++) {
    th[i] = F(); ra[i] = F(); at[i] = F(); re[i] = F(); mk[i] = F(); so[i] = I(); bb[i] = I();
  }
  float mix = F(), out = F();
  omx_mbcomp_instance_resolve(s, bypass, bands, xo, th, ra, at, re, mk, so, bb, mix, out);
}

#define ROW(prefix, T) {#prefix, sizeof(T), prefix##_init, prefix##_resolve, prefix##_run}
static const struct fx FX[] = {
    ROW(chorus, OmxChorusInstance),   ROW(comp, OmxCompInstance),       ROW(deesser, OmxDeesserInstance),
    ROW(delay, OmxDelayInstance),     ROW(doubler, OmxDoublerInstance), ROW(drive, OmxDriveInstance),
    ROW(dyneq, OmxDyneqInstance),     ROW(eq, OmxEqInstance),           ROW(flanger, OmxFlangerInstance),
    ROW(gate, OmxGateInstance),       ROW(geq, OmxGeqInstance),         ROW(leveler, OmxLevelerInstance),
    ROW(limiter, OmxLimiterInstance), ROW(mbcomp, OmxMbcompInstance),   ROW(phaser, OmxPhaserInstance),
    ROW(pitch, OmxPitchInstance),     ROW(plosive, OmxPlosiveInstance), ROW(reverb, OmxReverbInstance),
    ROW(rotary, OmxRotaryInstance),   ROW(suboct, OmxSuboctInstance),   ROW(tone, OmxToneInstance),
    ROW(transient, OmxTransientInstance), ROW(tremolo, OmxTremoloInstance), ROW(trim, OmxTrimInstance),
    ROW(width, OmxWidthInstance),
};
#define FX_COUNT (sizeof FX / sizeof FX[0])

static void *fx_alloc(size_t size) {
  size = (size + 63u) & ~(size_t)63u;
  void *p = aligned_alloc(64, size);
  /* not a property: malloc failed */
  if (!p) abort();
  memset(p, 0xA5, size); /* the face's init must set every byte it reads */
  return p;
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  struct fuzz_in in = fuzz_in(data, size);
  const struct fx *fx = &FX[fuzz_u8(&in) % FX_COUNT];
  const uint8_t flags = fuzz_u8(&in);
  const unsigned bmode = (unsigned)(flags >> 1);
  const float rate = (flags & 1u) ? fuzz_range(&in, 8000.0f, 768000.0f) : fuzz_rate(&in);

  fuzz_rate_undeclared = !omx_rate_is_declared(rate);
  char ctx[64];
  snprintf(ctx, sizeof ctx, "%s at %g Hz", fx->name, (double)rate);
  fuzz_ledger_reset();
  void *a = fx_alloc(fx->size), *b = fx_alloc(fx->size);
  const int ra = fx->init(a, rate), rb = fx->init(b, rate);
  /* Two inits at one rate answer the same.
   * mutant: include/omxdsp/fx/omx_trim_instance.h:69 `return 1;` -> `{ static int calls; return calls++ % 2; }`
   * input: trim-neutral */
  if (!(ra == rb)) {
    FUZZ_SAY("%s: two inits at %g disagree (%d, %d)", fx->name, (double)rate, ra, rb);
    abort();
  }
  fuzz_ledger_check(ctx, omx_rate_is_declared(rate), bmode & 1u);
  const int ready = ra;

  for (int step = 0; step < STEPS_MAX && in.n > 0; step++) {
    const int bypass = (int)fuzz_u8(&in) & 1;
    /* the ports: the words the resolve reads are the next bytes of the input; it works on a copy
     * of the cursor so both instances take the same ones, and the real cursor then skips them. */
    struct fuzz_in pa = in, pb = in;
    fx->resolve(a, bypass, &pa);
    fx->resolve(b, bypass, &pb);
    in = pa;
    fuzz_ledger_check(ctx, omx_rate_is_declared(rate), bmode & 1u);

    const uint32_t n = 1u + fuzz_u16(&in) % BLOCK_MAX;
    float il[BLOCK_MAX], ir[BLOCK_MAX], ol[BLOCK_MAX], orr[BLOCK_MAX], al[BLOCK_MAX], ar[BLOCK_MAX];
    fuzz_block(&in, il, n, bmode);
    fuzz_block(&in, ir, n, bmode);
    memcpy(al, il, n * sizeof(float));
    memcpy(ar, ir, n * sizeof(float));
    fx->run(a, al, ar, al, ar, n);
    fx->run(b, il, ir, ol, orr, n);

    /* Aliasing is safe: running in place gives the samples of running out of place, bit for bit.
     * mutant: include/omxdsp/fx/omx_trim_instance.h:95 `if (out_l != in_l) memmove` -> `if (out_l == in_l) out_l[0] += 1.0f; else memmove`
     * input: trim-neutral */
    if (!(memcmp(al, ol, n * sizeof(float)) == 0 && memcmp(ar, orr, n * sizeof(float)) == 0)) {
      FUZZ_SAY("%s: running in place gives other samples than running out of place", fx->name);
      abort();
    }
    if (!ready) {
      /* A refused init leaves run() the identity, bit for bit, whatever the ports say.
       * mutant: include/omxdsp/fx/omx_limiter_instance.h:137 `if (!s || !s->ready) return;` -> `if (!s || !s->ready) { out_l[0] = 0.5f; return; }`
       * input: refused-rate */
      if (!(memcmp(il, ol, n * sizeof(float)) == 0 && memcmp(ir, orr, n * sizeof(float)) == 0)) {
        FUZZ_SAY("%s: a refused init leaves run() other than the identity", fx->name);
        abort();
      }
    } else if (!(bmode & 1u)) {
      /* An instance that took finite samples gives finite samples back, at any port value.
       * mutant: include/omxdsp/fx/omx_trim_instance.h:99 `out_l[i] *= omx_ramp_at(g, i)` -> `out_l[i] = NAN`
       * input: trim-neutral */
      if (!(fuzz_all_finite(ol, n) && fuzz_all_finite(orr, n))) {
        FUZZ_SAY("%s: finite samples in, a non-finite sample out", fx->name);
        abort();
      }
    }
    fuzz_ledger_check(ctx, omx_rate_is_declared(rate), bmode & 1u);
  }
  free(a);
  free(b);
  return 0;
}
