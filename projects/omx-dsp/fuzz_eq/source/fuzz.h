// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>

/* What every libFuzzer harness in fuzz/ shares: a cursor over the input, the readers that
 * turn its bytes into the words a host hands the library, the block filler and the check
 * that no contract was recorded.
 *
 * The cursor is TOTAL. Reading past the end of the input yields zeros, never a failure, so
 * every input decodes to some sequence of calls and the end of the input ends the sequence.
 * Nothing here reads a clock, the environment, a file or the network.
 *
 * A harness is built with -DOMX_CONTRACTS (the library's own PRE/POST laws record into a
 * ledger, never abort) and defines OMX_CONTRACT_STORAGE before including this header, so the
 * laws are checked on every call the input makes. */
#ifndef OMXDSP_FUZZ_H
#define OMXDSP_FUZZ_H

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <omxdsp/omx_contract.h>

/* The two laws a harness expects to be broken never take a slot of the ledger, which keeps only
 * OMX_CONTRACT_MAX records. An instance face at 32, 64 or 128 kHz can record `rate-is-declared` once
 * per frame, and every law after those would be counted and never read. A harness that can see them
 * includes this header before the library's, so the library's inline code calls this, and sets
 * fuzz_rate_undeclared while the rate in force is not a declared one. */
#ifdef OMX_CONTRACTS
static int fuzz_rate_undeclared;
static inline void fuzz_contract_note(int ok, const char *stage, const char *token, const char *kind, uint32_t frame) {
  const int expected = strcmp(token, "bands-partition-unity") == 0 ||
                       (fuzz_rate_undeclared && strcmp(token, "rate-is-declared") == 0);
  omx_contract_note(ok || expected, stage, token, kind, frame);
}
#define omx_contract_note fuzz_contract_note
#endif

struct fuzz_in {
  const uint8_t *p;
  size_t n;
};

static inline struct fuzz_in fuzz_in(const uint8_t *data, size_t size) {
  struct fuzz_in in = {data, size};
  return in;
}

static inline uint8_t fuzz_u8(struct fuzz_in *in) {
  if (in->n == 0) return 0;
  in->n--;
  return *in->p++;
}

/* Little-endian, like every multi-byte field the harnesses invent. */
static inline uint16_t fuzz_u16(struct fuzz_in *in) {
  uint16_t lo = fuzz_u8(in);
  return (uint16_t)(lo | (uint16_t)fuzz_u8(in) << 8);
}

static inline uint32_t fuzz_u32(struct fuzz_in *in) {
  uint32_t lo = fuzz_u16(in);
  return lo | (uint32_t)fuzz_u16(in) << 16;
}

/* Any float: the four bytes are the IEEE word, so NaN, both infinities, denormals and
 * every magnitude are reachable, which is what a host's control port can hold. */
static inline float fuzz_f32(struct fuzz_in *in) {
  uint32_t w = fuzz_u32(in);
  float f;
  memcpy(&f, &w, sizeof f);
  return f;
}

/* Any double. */
static inline double fuzz_f64(struct fuzz_in *in) {
  uint64_t w = fuzz_u32(in);
  w |= (uint64_t)fuzz_u32(in) << 32;
  double d;
  memcpy(&d, &w, sizeof d);
  return d;
}

/* Any int a port can hold. */
static inline int fuzz_int(struct fuzz_in *in) { return (int)fuzz_u32(in); }

/* A float in [lo, hi] from two bytes: the sweeps a UI makes, reaching both ends exactly. */
static inline float fuzz_range(struct fuzz_in *in, float lo, float hi) {
  return lo + (hi - lo) * ((float)fuzz_u16(in) / 65535.0f);
}

/* A value in [0, n). */
static inline uint32_t fuzz_below(struct fuzz_in *in, uint32_t n) { return n ? fuzz_u8(in) % n : 0u; }

/* One of the nine rates the oracle grid declares. */
static inline float fuzz_rate(struct fuzz_in *in) {
  static const float rates[OMX_ORACLE_FULL_RATES_COUNT] = OMX_ORACLE_FULL_RATES_INIT;
  return rates[fuzz_below(in, OMX_ORACLE_FULL_RATES_COUNT)];
}

/* A block of n samples. Bit 0 of `mode` makes it HOSTILE (any float word per sample: NaN,
 * Inf, denormals); otherwise every sample is finite, in [-2^k, 2^k] with k from the mode's
 * higher bits (0..4), from a signed 16-bit word, so a loud programme and a silent one are
 * both reachable and the finite-in, finite-out laws are in force. */
static inline void fuzz_block(struct fuzz_in *in, float *b, uint32_t n, unsigned mode) {
  const float scale = (float)(1u << ((mode >> 1) % 5u)) / 32768.0f;
  for (uint32_t i = 0; i < n; i++) b[i] = (mode & 1u) ? fuzz_f32(in) : (float)(int16_t)fuzz_u16(in) * scale;
}

/* What a check says before its abort(): the property and the detail. Each check is its own
 * `if (...) abort();` in the harness, with its comment above it, so that the build contract of
 * OSS Verify reads and measures it; libFuzzer then writes the input that did it. */
#define FUZZ_SAY(...)                                      \
  do {                                                     \
    fprintf(stderr, "fuzz property broken: " __VA_ARGS__); \
    fputc('\n', stderr);                                   \
  } while (0)

/* Every sample finite: the harnesses' own reading, not the library's omx_block_finite. */
static inline int fuzz_all_finite(const float *b, uint32_t n) {
  for (uint32_t i = 0; i < n; i++)
    if (!(b[i] - b[i] == 0.0f)) return 0;
  return 1;
}

/* The ledger the library's contracts record into (the build defines OMX_CONTRACTS). A call a
 * harness makes inside every PRE it states breaks no law, so the ledger stays empty; a record
 * names the stage and the token that failed. `ctx` says where in the input's story.
 *
 * One law is expected and skipped: the instance faces take the nine rates of the oracle grid, of
 * which 32, 64 and 128 kHz are not declared rates, and at those every design records
 * `rate-is-declared` by design (the instance tests say so). `declared` is whether the
 * rate in force is a declared one; a record of that token is read as broken only when it is.
 * A second is skipped: the crossover's `bands-partition-unity` (lo + hi equals the all-pass) is a law
 * of one design. A multiband stage whose corner moves between two blocks carries the old design's
 * state into the new one, and the identity breaks for the transient, which the contracts build
 * records as a violation; a harness that moves the corners at random cannot read it. The identity is
 * held where the design is fixed, by the suite's own xover arm.
 * The ledger is emptied after each check, so a call's records are never pushed out by an earlier
 * call's, and fuzz_contract_note() keeps the two expected laws out of it, so they never push out
 * the records of the call that made them either. `hostile` is set while the blocks hold non-finite samples: the sanitizers are then the
 * oracle, and the ledger is only emptied. */
static inline void fuzz_ledger_check(const char *ctx, int declared, int hostile) {
#ifdef OMX_CONTRACTS
  if (hostile) { /* non-finite samples break the finite-in laws by the caller's own act: no law to read */
    omx_contract_reset();
    return;
  }
  const uint32_t n = atomic_load_explicit(&omx_contract_log.count, memory_order_relaxed);
  const uint32_t kept = n < OMX_CONTRACT_MAX ? n : OMX_CONTRACT_MAX;
  const struct omx_contract_record *broken = NULL;
  for (uint32_t i = 0; i < kept && !broken; i++) {
    const struct omx_contract_record *r = &omx_contract_log.rec[i];
    const int skipped = !omx_contract_record_ready(r) || (!declared && strcmp(r->token, "rate-is-declared") == 0) ||
                        strcmp(r->token, "bands-partition-unity") == 0;
    if (!skipped) broken = r;
  }
  /* No contract the library states is broken.
   * mutant: include/omxdsp/omx_onepole.h:120 `pole >= 0.0f && pole < 1.0f` -> `pole < 0.0f`
   * input: onepole
   * mutant: include/omxdsp/omx_dyn.h:745 `gain[i] = g * p->gc.makeup_lin;` -> `gain[i] = g * p->gc.makeup_lin * (prog && done + i >= 64u && !omx_rate_is_declared(p->prp[0].sr) ? 2.0f : 1.0f);`
   * input: comp-feedback-opto-64000 */
  if (broken) {
    FUZZ_SAY("%s: contract broken: %s %s %s (%u in all)", ctx, broken->stage, broken->kind, broken->token, (unsigned)n);
    abort();
  }
  omx_contract_reset();
#else
  (void)ctx;
  (void)declared;
  (void)hostile;
#endif
}

static inline void fuzz_ledger_clean(const char *ctx) { fuzz_ledger_check(ctx, 1, 0); }

/* Forget what an earlier input left in the ledger: each input starts clean. */
static inline void fuzz_ledger_reset(void) {
#ifdef OMX_CONTRACTS
  omx_contract_reset();
  atomic_store_explicit(&omx_contract_log.count, 0u, memory_order_relaxed);
#endif
}

#endif /* OMXDSP_FUZZ_H */
