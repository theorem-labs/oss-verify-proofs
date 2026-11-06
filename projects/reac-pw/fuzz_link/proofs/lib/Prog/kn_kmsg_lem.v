(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/bzip2/bzip2_compress_target/lib/K/A/L_hkit.v, with its module paths and module names changed; 801 of its 858 lines of code are new or changed and 196 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/Prog/reac_served_unmark_all.v; 70 of its 92 lines of code are new or changed and 836 lines of the source are left out. *)
(* reac-pw/fuzz_link, PLAIN build: kernel's message loop (0x143e4 .. 0x14df4), the part the block files share.

   The loop (kn_kmsg.v, `k_msgloop`) reads a kind byte and jumps through the table at .rodata 0x106c4 to one of
   the message kinds. Each kind is a lemma whose statement is fixed here (`k1_stmt` .. `k6_stmt`): from the
   kind's first block, with the kind byte read (the cursor at A), the machine reaches the latch 0x14de0 in the
   shape `k_after_msg` (kn_k0.v) names. Kinds 0 and 7 are kn_k07.v's `k_kind07`.
   This file also holds nl_end at +0xc28 (`k_c28`), which kinds 3, 4 and 5 end in. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf mk_call kn_nlk kn_kfr kn_k0
  nl_error_c.
Local Open Scope Z_scope.

(* the register map of the message loop: sp, gp, tp, s0 = the cursor, s3 = 1, s4 = w, s6 = k, s8 = &w.n,
   s10 = -4093 are fixed; the arguments name the other registers by their number *)
Abbreviation KR c k x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 :=
  (mkR x1 (Z_to_bv 64 (kSP c + -4336)) (kf_gp c) (kf_tp c) x5 x6 x7 (kf_a0 c) x9 x10 x11 x12 x13 x14 x15 x16 x17
       x18 (Z_to_bv 64 1) (Z_to_bv 64 (kSP c + -4216)) x21 (Z_to_bv 64 k) x23 (Z_to_bv 64 (kSP c + -120)) x25
       (Z_to_bv 64 (-4093)) x27 x28 x29 x30 x31) (only parsing).

(* the machine at pc with memory m and registers R, and kernel's goal *)
Abbreviation KG c pc m R :=
  (evt rsegs (kf_Q c) (MS R (kf_F c) (Z_to_bv 64 pc) (kf_fc c) None m (seg_rom rsegs))) (only parsing).

(* a smaller lower bound on the cursor accepts more states *)
Lemma k_after_msg_mono : forall c k A A' kbs j n ci mc,
  k_after_msg c k A kbs j n ci mc -> A <= A' -> k_after_msg c k A' kbs j n ci mc.
Proof.
  unfold k_after_msg. intros c k A A' kbs j n ci mc H L. intros. eapply H; [eassumption |]. lia.
Qed.

(* ==========================================================================
   The kinds: the statements kn_kmsg_k*.v prove
   ========================================================================== *)

(* kind 1, +0x294: nl_error(w, 0, -1) *)
Definition k1_stmt : Prop :=
  forall c, kf_ok c ->
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) (A : Z) (kbs : list byte) (j : Z) (la : list byte) (n ci mc k wn : Z),
  kmsg_st c m A kbs j la n ci mc wn 0 -> 0 <= k < mc -> k_after_msg c k A kbs j n ci mc ->
  KG c 0x14424 m (KR c k x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31).

(* kind 2, +0x880: one more byte c (0 when the input is empty), then nl_error(w, codes[c % 4], cut);
   s1 = the bytes left, a0 = the bytes left before the kind byte, a1 = the kind byte's address *)
Definition k2_stmt : Prop :=
  forall c, kf_ok c ->
  forall (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) (A : Z) (kbs : list byte) (j : Z) (la : list byte) (n ci mc k wn : Z),
  kmsg_st c m A kbs j la n ci mc wn 0 -> 1 <= A -> 0 <= k < mc -> k_after_msg c k A kbs j n ci mc ->
  KG c 0x14a10 m (KR c k x1 x5 x6 x7 (Z_to_bv 64 (kWN c - A)) (Z_to_bv 64 (kWN c - A + 1))
                     (Z_to_bv 64 (kWP c + A - 1)) x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31).

(* kind 3, +0x860: nl_begin(NL_DONE), put32(0), nl_end *)
Definition k3_stmt : Prop :=
  forall c, kf_ok c ->
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) (A : Z) (kbs : list byte) (j : Z) (la : list byte) (n ci mc k wn : Z),
  kmsg_st c m A kbs j la n ci mc wn 0 -> 0 <= k < mc -> k_after_msg c k A kbs j n ci mc ->
  KG c 0x149f0 m (KR c k x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31).

(* kind 4, +0x8e4: nl_begin(20), put("01234567", 8), nl_end *)
Definition k4_stmt : Prop :=
  forall c, kf_ok c ->
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) (A : Z) (kbs : list byte) (j : Z) (la : list byte) (n ci mc k wn : Z),
  kmsg_st c m A kbs j la n ci mc wn 0 -> 0 <= k < mc -> k_after_msg c k A kbs j n ci mc ->
  KG c 0x14a74 m (KR c k x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31).

(* kind 5, +0x904: nl_begin(RTM_NEWLINK_), put32(0), nl_end *)
Definition k5_stmt : Prop :=
  forall c, kf_ok c ->
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) (A : Z) (kbs : list byte) (j : Z) (la : list byte) (n ci mc k wn : Z),
  kmsg_st c m A kbs j la n ci mc wn 0 -> 0 <= k < mc -> k_after_msg c k A kbs j n ci mc ->
  KG c 0x14a94 m (KR c k x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31).

(* kind 6, +0x89c: put32(8), put32(NL_DONE) *)
Definition k6_stmt : Prop :=
  forall c, kf_ok c ->
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) (A : Z) (kbs : list byte) (j : Z) (la : list byte) (n ci mc k wn : Z),
  kmsg_st c m A kbs j la n ci mc wn 0 -> 0 <= k < mc -> k_after_msg c k A kbs j n ci mc ->
  KG c 0x14a2c m (KR c k x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31).

(* ==========================================================================
   Tactics
   ========================================================================== *)

(* the register map the step tactics leave, back into `mkR` form (copied from
   lib/Prog/reac_served_unmark_all.v) *)
Ltac fold_mkR :=
  match goal with
  | |- context [TNode
      (TNode (TNode (TNode (TNode (TNode TEmpty (Some ?x31) TEmpty) (Some ?x15) TEmpty) (Some ?x7) (TNode TEmpty (Some ?x23) TEmpty)) (Some ?x3) (TNode (TNode TEmpty (Some ?x19) TEmpty) (Some ?x11) (TNode TEmpty (Some ?x27) TEmpty)))
         (Some ?x1) (TNode (TNode (TNode TEmpty (Some ?x17) TEmpty) (Some ?x9) (TNode TEmpty (Some ?x25) TEmpty)) (Some ?x5) (TNode (TNode TEmpty (Some ?x21) TEmpty) (Some ?x13) (TNode TEmpty (Some ?x29) TEmpty))))
      None
      (TNode (TNode (TNode (TNode TEmpty (Some ?x16) TEmpty) (Some ?x8) (TNode TEmpty (Some ?x24) TEmpty)) (Some ?x4) (TNode (TNode TEmpty (Some ?x20) TEmpty) (Some ?x12) (TNode TEmpty (Some ?x28) TEmpty))) (Some ?x2)
         (TNode (TNode (TNode TEmpty (Some ?x18) TEmpty) (Some ?x10) (TNode TEmpty (Some ?x26) TEmpty)) (Some ?x6) (TNode (TNode TEmpty (Some ?x22) TEmpty) (Some ?x14) (TNode TEmpty (Some ?x30) TEmpty))))] =>
      change (TNode
      (TNode (TNode (TNode (TNode (TNode TEmpty (Some x31) TEmpty) (Some x15) TEmpty) (Some x7) (TNode TEmpty (Some x23) TEmpty)) (Some x3) (TNode (TNode TEmpty (Some x19) TEmpty) (Some x11) (TNode TEmpty (Some x27) TEmpty)))
         (Some x1) (TNode (TNode (TNode TEmpty (Some x17) TEmpty) (Some x9) (TNode TEmpty (Some x25) TEmpty)) (Some x5) (TNode (TNode TEmpty (Some x21) TEmpty) (Some x13) (TNode TEmpty (Some x29) TEmpty))))
      None
      (TNode (TNode (TNode (TNode TEmpty (Some x16) TEmpty) (Some x8) (TNode TEmpty (Some x24) TEmpty)) (Some x4) (TNode (TNode TEmpty (Some x20) TEmpty) (Some x12) (TNode TEmpty (Some x28) TEmpty))) (Some x2)
         (TNode (TNode (TNode TEmpty (Some x18) TEmpty) (Some x10) (TNode TEmpty (Some x26) TEmpty)) (Some x6) (TNode (TNode TEmpty (Some x22) TEmpty) (Some x14) (TNode TEmpty (Some x30) TEmpty)))))
      with (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
  end.

(* kmsg_st back from the named hypotheses kmsg_unpack gave and the walk carried: every cell by the hypothesis
   of its shape, every range by lia; a range whose variable a later piece fixes is left for `all: lia` *)
Ltac kpack :=
  eapply kmsg_intro; unfold kspill, kfrs, kW; first [eassumption | lia | idtac].

(* at the latch 0x14de0 with the state packed: the continuation `k_after_msg` *)
Ltac kto_latch HK :=
  fold_mkR; unfold k_after_msg in HK; eapply HK; [kpack; lia |]; lia.

(* g_nl's length, for the disjointness of every store from g_nl *)
Ltac kgl GI :=
  let GL := fresh "GL" in pose proof (proj1 GI) as GL; unfold NK_SIZE in GL.

(* ==========================================================================
   nl_end at +0xc28 (0x14db8): a0 = w + at, a1 = at, a2 = w.n = N
   ========================================================================== *)

Lemma k_c28 : forall c, kf_ok c ->
  forall (x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) (A : Z) (kbs : list byte) (j : Z) (la : list byte) (n ci mc k p0 N wf : Z),
  kmsg_st c m A kbs j la n ci mc N wf -> 0 <= p0 <= N -> k_after_msg c k A kbs j n ci mc ->
  KG c 0x14db8 m (KR c k x1 x5 x6 x7 x9 (Z_to_bv 64 (kSP c + -4216 + p0)) (Z_to_bv 64 p0) (Z_to_bv 64 N)
                     x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31).
Proof.
  intros c HC x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 m A kbs j la n ci mc k p0 N wf
    ST HP HK.
  kctx c HC. kmsg_unpack ST. kgl GI.
  zstep. zstep.
  if_cases HB; zify_cond HB.
  - (* N < at + 4: no length *)
    kto_latch HK.
  - (* the length N - at as u32 at w + at *)
    do 8 zstep.
    kto_latch HK.
Qed.
