(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/bzip2/bzip2_compress_target/lib/K/A/L_hkit.v, with its module paths and module names changed; 801 of its 858 lines of code are new or changed and 196 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/Prog/reac_served_unmark_all.v; 70 of its 92 lines of code are new or changed and 836 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/Prog/kn_kmsg_lem.v, with its addresses and numbers changed; 106 of its 122 lines of code are new or changed and 76 lines of the source are left out. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf mk_call kn_nlk kn_kfr kn_k0 nl_error_c kn_kmsg_lem.
Local Open Scope Z_scope.

(* reac-pw/fuzz_link, PLAIN build: kinds 3 and 5 of kernel's message loop (kn_kmsg_lem.v `k3_stmt`, `k5_stmt`).

   Kind 3 (+0x860, 0x149f0) and kind 5 (+0x904, 0x14a94) are nl_begin(type), put32(0), nl_end, with type 3
   (NL_DONE) and 0x10 (RTM_NEWLINK_). nl_begin is five puts (len 0, type, flags 0, seq 1, pid 0); each put is a
   fit / no-fit diamond (a put that does not fit sets w.full and writes nothing). At the kind's entry
   a1 := at = w.n and a0 := w + at; both stay to nl_end at +0xc28 (kn_kmsg_lem.v `k_c28`).

   The cut, at the join blocks the two kinds share (last first):
     k_ab0  +0xab0 (0x14c40): put32(0), then nl_end
     k_a50  +0xa50 (0x14be0): put32(seq = 1), put32(pid = 0)
     k_a10  +0xa10 (0x14ba0): the fitted put16(type) stores, then put16(flags = 0)
   and each kind walks put32(len = 0) and the type's fit test inline to +0xa10 (fit) or +0xa30 (no fit: two
   instructions, walked inline to +0xa50). *)

(* +0xab0: a0 = w + at, a1 = at, a2 = w.n = N *)
Lemma k_ab0 : forall c, kf_ok c ->
  forall (x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) (A : Z) (kbs : list byte) (j : Z) (la : list byte) (n ci mc k p0 N wf : Z),
  kmsg_st c m A kbs j la n ci mc N wf -> 0 <= p0 <= N -> k_after_msg c k A kbs j n ci mc ->
  KG c 0x14c40 m (KR c k x1 x5 x6 x7 x9 (Z_to_bv 64 (kSP c + -4216 + p0)) (Z_to_bv 64 p0) (Z_to_bv 64 N)
                     x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31).
Proof.
  intros c HC x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 m A kbs j la n ci mc k p0 N wf
    ST HP HK.
  kctx c HC. kmsg_unpack ST. kgl GI.
  do 3 zstep.
  if_cases HB; zify_cond HB.
  - (* N + 4 > 4096: full = 1 (+0xbd0) *)
    do 2 zstep.
    fold_mkR. eapply (k_c28 c HC); [kpack; lia | lia | exact HK].
  - (* four zero bytes at w + N, w.n = N + 4 (+0xabc, +0xc24) *)
    do 9 zstep.
    fold_mkR. eapply (k_c28 c HC); [kpack; lia | lia | exact HK].
Qed.

(* +0xa50: a0 = w + at, a1 = at, a2 = w.n = N *)
Lemma k_a50 : forall c, kf_ok c ->
  forall (x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) (A : Z) (kbs : list byte) (j : Z) (la : list byte) (n ci mc k p0 N wf : Z),
  kmsg_st c m A kbs j la n ci mc N wf -> 0 <= p0 <= N -> k_after_msg c k A kbs j n ci mc ->
  KG c 0x14be0 m (KR c k x1 x5 x6 x7 x9 (Z_to_bv 64 (kSP c + -4216 + p0)) (Z_to_bv 64 p0) (Z_to_bv 64 N)
                     x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31).
Proof.
  intros c HC x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 m A kbs j la n ci mc k p0 N wf
    ST HP HK.
  kctx c HC. kmsg_unpack ST. kgl GI.
  do 3 zstep.
  if_cases HB; zify_cond HB.
  - (* N + 4 > 4096: full = 1 (+0xa88) *)
    do 2 zstep.
    fold_mkR. eapply (k_ab0 c HC); [kpack; lia | lia | exact HK].
  - (* seq = 1 at w + N, w.n = N + 4 (+0xa5c), then the pid's fit test *)
    do 11 zstep.
    if_cases HB2; zify_cond HB2.
    + (* pid = 0 at w + N + 4, w.n = N + 8 (+0xa90) *)
      do 8 zstep.
      fold_mkR. eapply (k_ab0 c HC); [kpack; lia | lia | exact HK].
    + (* no pid: full = 1 (+0xa88) *)
      do 2 zstep.
      fold_mkR. eapply (k_ab0 c HC); [kpack; lia | lia | exact HK].
Qed.

(* +0xa10: the type put fits (N + 2 <= 4096): a2 = w + N, a3 = the type word *)
Lemma k_a10 : forall c, kf_ok c ->
  forall (x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) (A : Z) (kbs : list byte) (j : Z) (la : list byte) (n ci mc k p0 N wf : Z),
  kmsg_st c m A kbs j la n ci mc N wf -> 0 <= p0 <= N -> N + 2 <= 4096 -> k_after_msg c k A kbs j n ci mc ->
  KG c 0x14ba0 m (KR c k x1 x5 x6 x7 x9 (Z_to_bv 64 (kSP c + -4216 + p0)) (Z_to_bv 64 p0)
                     (Z_to_bv 64 (kSP c + -4216 + N)) x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31).
Proof.
  intros c HC x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 m A kbs j la n ci mc k p0 N wf
    ST HP HN HK.
  kctx c HC. kmsg_unpack ST. kgl GI.
  do 8 zstep.
  if_cases HB; zify_cond HB.
  - (* flags = 0 at w + N + 2, w.n = N + 4 (+0xa38) *)
    do 6 zstep.
    fold_mkR. eapply (k_a50 c HC); [kpack; lia | lia | exact HK].
  - (* no flags: full = 1 (+0xa30) *)
    do 2 zstep.
    fold_mkR. eapply (k_a50 c HC); [kpack; lia | lia | exact HK].
Qed.

(* kind 3, +0x860: len 0 (+0x948 fit | +0x874 full), the type's fit test at +0x964, then +0xa10 with
   type 3 (+0x974) or +0xa30 (full) *)
Lemma k3 : k3_stmt.
Proof.
  intros c HC x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 m A kbs j la n ci
    mc k wn ST HKR HK.
  kctx c HC. kmsg_unpack ST. kgl GI.
  do 5 zstep.
  if_cases HB; zify_cond HB.
  - (* len = 0 at w + wn, w.n = wn + 4 (+0x948) *)
    do 7 zstep.
    do 4 zstep.
    if_cases HB2; zify_cond HB2.
    + (* no type: full = 1 (+0xa30) *)
      do 2 zstep.
      fold_mkR. eapply (k_a50 c HC); [kpack; lia | lia | exact HK].
    + (* type 3 (+0x974) *)
      do 3 zstep.
      fold_mkR. eapply (k_a10 c HC); [kpack; lia | lia | lia | exact HK].
  - (* no len: full = 1 (+0x874) *)
    do 3 zstep.
    do 4 zstep.
    if_cases HB2; zify_cond HB2.
    + (* no type: full = 1 (+0xa30) *)
      do 2 zstep.
      fold_mkR. eapply (k_a50 c HC); [kpack; lia | lia | exact HK].
    + (* type 3 (+0x974) *)
      do 3 zstep.
      fold_mkR. eapply (k_a10 c HC); [kpack; lia | lia | lia | exact HK].
Qed.

(* kind 5, +0x904: len 0 (+0x9dc fit | +0x918 full), the type's fit test at +0x9f8, then +0xa10 with
   type 0x10 (+0xa08) or +0xa30 (full) *)
Lemma k5 : k5_stmt.
Proof.
  intros c HC x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 m A kbs j la n ci
    mc k wn ST HKR HK.
  kctx c HC. kmsg_unpack ST. kgl GI.
  do 5 zstep.
  if_cases HB; zify_cond HB.
  - (* len = 0 at w + wn, w.n = wn + 4 (+0x9dc) *)
    do 7 zstep.
    do 4 zstep.
    if_cases HB2; zify_cond HB2.
    + (* no type: full = 1 (+0xa30) *)
      do 2 zstep.
      fold_mkR. eapply (k_a50 c HC); [kpack; lia | lia | exact HK].
    + (* type 0x10 (+0xa08) *)
      do 2 zstep.
      fold_mkR. eapply (k_a10 c HC); [kpack; lia | lia | lia | exact HK].
  - (* no len: full = 1 (+0x918) *)
    do 3 zstep.
    do 4 zstep.
    if_cases HB2; zify_cond HB2.
    + (* no type: full = 1 (+0xa30) *)
      do 2 zstep.
      fold_mkR. eapply (k_a50 c HC); [kpack; lia | lia | exact HK].
    + (* type 0x10 (+0xa08) *)
      do 2 zstep.
      fold_mkR. eapply (k_a10 c HC); [kpack; lia | lia | lia | exact HK].
Qed.
