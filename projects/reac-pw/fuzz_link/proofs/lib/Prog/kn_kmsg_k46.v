(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/bzip2/bzip2_compress_target/lib/K/A/L_hkit.v, with its module paths and module names changed; 801 of its 858 lines of code are new or changed and 196 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/Prog/reac_served_unmark_all.v; 70 of its 92 lines of code are new or changed and 836 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/Prog/kn_kmsg_lem.v, with its addresses and numbers changed; 91 of its 108 lines of code are new or changed and 75 lines of the source are left out. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf mk_call kn_nlk kn_kfr kn_k0 nl_error_c kn_kmsg_lem.
Local Open Scope Z_scope.

(* reac-pw/fuzz_link, PLAIN build: kernel's message kinds 4 and 6 (kn_kmsg_lem.v `k4_stmt`, `k6_stmt`).

   Kind 6, +0x89c (0x14a2c): put32(8), put32(NL_DONE). Two fit / no-fit diamonds, walked in one lemma `k6`
   (three paths, each ends at the latch +0xc50).

   Kind 4, +0x8e4 (0x14a74): nl_begin(20) (puts 4, 2, 2, 4, 4), put("01234567", 8), nl_end. At entry
   a1 := at = w.n and a0 := w + at, kept to nl_end at +0xc28 (`k_c28`, kn_kmsg_lem.v). The chain of diamonds
   is cut at its join blocks, each a lemma from that block with a0 = w + at, a1 = at, a2 = N = w.n now:
     k_bc0 (+0xbc0, 0x14d50): put "01234567", then k_c28
     k_b60 (+0xb60, 0x14cf0): put32 seq 1 and put32 0, then k_bc0
     k_99c (+0x99c, 0x14b2c): put16 20 and put16 flags 0, then k_b60
     k4    (+0x8e4, 0x14a74): put32 len 0, then k_99c. *)

(* at a join block with the state packed: the join lemma L (a0 = w + at, a1 = at, a2 = w.n) *)
Ltac kjoin L c HC HK :=
  fold_mkR; eapply (L c HC); [kpack; lia | lia | exact HK].

(* +0xbc0: put(w, "01234567", 8), then nl_end *)
Lemma k_bc0 : forall c, kf_ok c ->
  forall (x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) (A : Z) (kbs : list byte) (j : Z) (la : list byte) (n ci mc k p0 N wf : Z),
  kmsg_st c m A kbs j la n ci mc N wf -> 0 <= p0 <= N -> k_after_msg c k A kbs j n ci mc ->
  KG c 0x14d50 m (KR c k x1 x5 x6 x7 x9 (Z_to_bv 64 (kSP c + -4216 + p0)) (Z_to_bv 64 p0) (Z_to_bv 64 N)
                     x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31).
Proof.
  intros c HC x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 m A kbs j la n ci mc k p0 N wf
    ST HP HK.
  kctx c HC. kmsg_unpack ST. kgl GI.
  do 4 zstep.
  if_cases HB; zify_cond HB.
  - (* N + 8 <= 4096: the 8 bytes at w + N, w.n = N + 8 *)
    do 20 zstep. kjoin k_c28 c HC HK.
  - (* no room: full = 1 *)
    do 2 zstep. kjoin k_c28 c HC HK.
Qed.

(* +0xb60: put32(w, seq = 1), put32(w, pid = 0), then k_bc0 *)
Lemma k_b60 : forall c, kf_ok c ->
  forall (x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) (A : Z) (kbs : list byte) (j : Z) (la : list byte) (n ci mc k p0 N wf : Z),
  kmsg_st c m A kbs j la n ci mc N wf -> 0 <= p0 <= N -> k_after_msg c k A kbs j n ci mc ->
  KG c 0x14cf0 m (KR c k x1 x5 x6 x7 x9 (Z_to_bv 64 (kSP c + -4216 + p0)) (Z_to_bv 64 p0) (Z_to_bv 64 N)
                     x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31).
Proof.
  intros c HC x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 m A kbs j la n ci mc k p0 N wf
    ST HP HK.
  kctx c HC. kmsg_unpack ST. kgl GI.
  do 3 zstep.
  if_cases HB; zify_cond HB.
  - (* N + 4 > 4096: full = 1 *)
    do 2 zstep.
    kjoin k_bc0 c HC HK.
  - (* 1 at w + N, w.n = N + 4 *)
    do 11 zstep.
    if_cases HB2; zify_cond HB2.
    + (* 0 at w + N + 4, w.n = N + 8 *)
      do 8 zstep.
      kjoin k_bc0 c HC HK.
    + (* N + 8 > 4096: full = 1 *)
      do 2 zstep.
      kjoin k_bc0 c HC HK.
Qed.

(* +0x99c: put16(w, type = 20), put16(w, flags = 0), then k_b60 *)
Lemma k_99c : forall c, kf_ok c ->
  forall (x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) (A : Z) (kbs : list byte) (j : Z) (la : list byte) (n ci mc k p0 N wf : Z),
  kmsg_st c m A kbs j la n ci mc N wf -> 0 <= p0 <= N -> k_after_msg c k A kbs j n ci mc ->
  KG c 0x14b2c m (KR c k x1 x5 x6 x7 x9 (Z_to_bv 64 (kSP c + -4216 + p0)) (Z_to_bv 64 p0) (Z_to_bv 64 N)
                     x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31).
Proof.
  intros c HC x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 m A kbs j la n ci mc k p0 N wf
    ST HP HK.
  kctx c HC. kmsg_unpack ST. kgl GI.
  do 4 zstep.
  if_cases HB; zify_cond HB.
  - (* N + 2 > 4096: full = 1 *)
    do 2 zstep.
    kjoin k_b60 c HC HK.
  - (* 20, 0 at w + N, w.n = N + 2 *)
    do 10 zstep.
    if_cases HB2; zify_cond HB2.
    + (* 0, 0 at w + N + 2, w.n = N + 4 *)
      do 6 zstep.
      kjoin k_b60 c HC HK.
    + (* N + 4 > 4096: full = 1 *)
      do 2 zstep.
      kjoin k_b60 c HC HK.
Qed.

(* kind 4, +0x8e4: put32(w, len = 0) at at = w.n, then k_99c *)
Lemma k4 : k4_stmt.
Proof.
  unfold k4_stmt.
  intros c HC x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 m A kbs j la
    n ci mc k wn ST HKR HK.
  kctx c HC. kmsg_unpack ST. kgl GI.
  do 5 zstep.
  if_cases HB; zify_cond HB.
  - (* 0, 0, 0, 0 at w + wn, w.n = wn + 4 *)
    do 7 zstep.
    kjoin k_99c c HC HK.
  - (* wn + 4 > 4096: full = 1 *)
    do 3 zstep.
    kjoin k_99c c HC HK.
Qed.

(* kind 6, +0x89c: put32(w, 8), put32(w, NL_DONE = 3) *)
Lemma k6 : k6_stmt.
Proof.
  unfold k6_stmt.
  intros c HC x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 m A kbs j la
    n ci mc k wn ST HKR HK.
  kctx c HC. kmsg_unpack ST. kgl GI.
  do 4 zstep.
  if_cases HB; zify_cond HB.
  - (* wn + 4 > 4096: full = 1 *)
    do 2 zstep.
    kto_latch HK.
  - (* 8, 0, 0, 0 at w + wn, w.n = wn + 4 *)
    do 12 zstep.
    if_cases HB2; zify_cond HB2.
    + (* 3, 0, 0, 0 at w + wn + 4, w.n = wn + 8 *)
      do 10 zstep.
      kto_latch HK.
    + (* wn + 8 > 4096: full = 1 *)
      do 2 zstep.
      kto_latch HK.
Qed.
