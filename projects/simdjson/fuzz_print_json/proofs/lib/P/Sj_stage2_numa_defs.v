(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage2 SjLeaves.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_stage2_defs Sj_stage2_numkit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section NumADefs.
  Variable E : s2env.
  Notation bs := (e_bs E).

  Definition NSL (neg : Z) (s : st) (j0 j8 j16 j24 j56 j72 : list byte) : list cell :=
    [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; C8 (Z_to_bv 64 neg); C8 (Z_to_bv 64 (depth s));
     C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); CB 8 j56; C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j72].

  Lemma MEMI_NSL : forall nxt neg s c0 c8 c16 c24 c56 c72 sc fc m1,
    MEMI E nxt [c0; c8; c16; c24; C8 (Z_to_bv 64 neg); C8 (Z_to_bv 64 (depth s)); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); c56;
                C8 (Z_to_bv 64 (e_SBUF E + sb s)); c72] sc fc m1 ->
    csize c0 = 8%nat -> csize c8 = 8%nat -> csize c16 = 8%nat -> csize c24 = 8%nat -> csize c56 = 8%nat -> csize c72 = 8%nat ->
    MEMI E nxt (NSL neg s (cbytes c0) (cbytes c8) (cbytes c16) (cbytes c24) (cbytes c56) (cbytes c72)) sc fc m1.
  Proof.
    intros nxt neg s c0 c8 c16 c24 c56 c72 sc fc m1 H E0 E8 E16 E24 E56 E72. unfold NSL.
    apply (MEMI_forget8 E nxt [] c0 _ sc fc m1 E0) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_] c8 _ sc fc m1 E8) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_; _] c16 _ sc fc m1 E16) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_; _; _] c24 _ sc fc m1 E24) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_; _; _; _; _; _; _] c56 _ sc fc m1 E56) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_; _; _; _; _; _; _; _; _] c72 _ sc fc m1 E72) in H. cbn [app] in H.
    exact H.
  Qed.

  Definition numa_scan_k (Q : machine_state -> Prop) (s : st) (neg : Z) (pc p : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa4 xa6 xa7 xs3 xs5 xs6 xs7 xs9 xs10 xs11 xt4 xt5 xt6 j0 j8 j16 j24 j56 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (NSL neg s j0 j8 j16 j24 j56 j72) (scopes s) fc m1 ->
      evt psegs Q (S2R E pc xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 (Z_to_bv 64 (e_off E (k s))) xa4 (Z_to_bv 64 (e_BUF E + p)) xa6 xa7 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xs3 (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 (Z_to_bv 64 (e_TAPE E + 8 * W s)) xs9 xs10 xs11 (Z_to_bv 64 (B bs p)) xt4 xt5 xt6 F fc m1).

  Definition numa_frac_k (Q : machine_state -> Prop) (s : st) (neg : Z) (p : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa4 xa6 xa7 xs3 xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j56 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (NSL neg s j0 j8 j16 j24 j56 j72) (scopes s) fc m1 ->
      evt psegs Q (S2R E 0x485e4 xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 (Z_to_bv 64 (e_off E (k s))) xa4 (Z_to_bv 64 (e_BUF E + p)) xa6 xa7 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xs3 (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 (Z_to_bv 64 (e_TAPE E + 8 * W s)) xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numa_flt_k (Q : machine_state -> Prop) (s : st) (neg : Z) (c : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs9 xs10 xs11 xt4 xt5 xt6 j0 j8 j16 j24 j56 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (NSL neg s j0 j8 j16 j24 j56 j72) (scopes s) fc m1 ->
      evt psegs Q (S2R E 0x48ab4 xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 (Z_to_bv 64 (e_off E (k s))) xa4 xa5 xa6 xa7 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xs3 (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 (Z_to_bv 64 (e_TAPE E + 8 * W s)) xs9 xs10 xs11 (Z_to_bv 64 (c)) xt4 xt5 xt6 F fc m1).

  Definition numa_int_k (Q : machine_state -> Prop) (s : st) (neg : Z) (p : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa6 xa7 xs3 xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j56 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (NSL neg s j0 j8 j16 j24 j56 j72) (scopes s) fc m1 ->
      evt psegs Q (S2R E 0x48d20 xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 xa3 xa4 (Z_to_bv 64 (e_BUF E + p)) xa6 xa7 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xs3 (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 (Z_to_bv 64 (e_TAPE E + 8 * W s)) xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numa_e48_k (Q : machine_state -> Prop) (s : st) (neg : Z) (q0 : Z) : Prop :=
    forall xra xt1 xt2 xs1 xa0 xa1 xa2 xa4 xa5 xa6 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 j0 j8 j16 j24 j56 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (NSL neg s j0 j8 j16 j24 j56 j72) (scopes s) fc m1 ->
      evt psegs Q (S2R E 0x48a40 xra (Z_to_bv 64 (B bs q0)) xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 (Z_to_bv 64 (e_off E (k s))) xa4 xa5 xa6 (Z_to_bv 64 (e_BUF E + q0)) (Z_to_bv 64 (e_BUF E + e_off E (k s))) xs3 (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 (Z_to_bv 64 (e_TAPE E + 8 * W s)) F fc m1).

  Definition numa_e98_k (Q : machine_state -> Prop) (s : st) (neg : Z) (c : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 j0 j8 j16 j24 j56 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (NSL neg s j0 j8 j16 j24 j56 j72) (scopes s) fc m1 ->
      evt psegs Q (S2R E 0x48a90 xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 (Z_to_bv 64 (e_off E (k s))) xa4 xa5 xa6 xa7 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xs3 (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (c)) xt4 xt5 (Z_to_bv 64 (e_TAPE E + 8 * W s)) F fc m1).

  Definition numa_i3f4_k (Q : machine_state -> Prop) (s : st) (neg : Z) (c : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j56 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (NSL neg s j0 j8 j16 j24 j56 j72) (scopes s) fc m1 ->
      evt psegs Q (S2R E 0x48dec xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 (Z_to_bv 64 (c)) (Z_to_bv 64 (81108)) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (e_BUF E + e_off E (k s))) (Z_to_bv 64 (e_TAPE E + 8 * W s)) (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numa_join_k (Q : machine_state -> Prop) (s : st) (neg : Z)  : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j56 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (NSL neg s j0 j8 j16 j24 j56 j72) (scopes s) fc m1 ->
      evt psegs Q (S2R E 0x48f68 xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 (Z_to_bv 64 (1)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (e_BUF E + e_off E (k s))) (Z_to_bv 64 (e_TAPE E + 8 * (W s + 2))) (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numa_cmp_k (Q : machine_state -> Prop) (s : st) (neg : Z) (e : Z) : Prop :=
    forall xra xt0 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j56 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (NSL neg s j0 j8 j16 j24 j56 j72) (scopes s) fc m1 ->
      evt psegs Q (S2R E 0x48b94 xra xt0 (Z_to_bv 64 (e)) xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (e_BUF E + e_off E (k s))) (Z_to_bv 64 (e_TAPE E + 8 * W s)) (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numa_tail_k (Q : machine_state -> Prop) (s : st) (neg : Z) (pc Wv : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j56 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (NSL neg s j0 j8 j16 j24 j56 j72) (scopes s) fc m1 ->
      evt psegs Q (S2R E pc xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (e_BUF E + e_off E (k s))) (Z_to_bv 64 (e_TAPE E + 8 * Wv)) (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numa_wr_k (Q : machine_state -> Prop) (s : st) (neg : Z) (Wv : Z) : Prop :=
    forall a0v xra xt0 xt1 xt2 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j56 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      (a0v = 0 \/ a0v = 9)%Z ->
      MEMI E (e_nxt0 E) (NSL neg s j0 j8 j16 j24 j56 j72) (scopes s) fc m1 ->
      evt psegs Q (S2R E 0x48e64 xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 (Z_to_bv 64 a0v) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (e_BUF E + e_off E (k s))) (Z_to_bv 64 (e_TAPE E + 8 * Wv)) (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition FSL (v8 v16 v24 : word) (neg : Z) (s : st) (j0 j72 : list byte) : list cell :=
    [CB 8 j0; C8 v8; C8 v16; C8 v24; C8 (Z_to_bv 64 neg); C8 (Z_to_bv 64 (depth s));
     C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j72].

  Definition numa_ftail_k (Q : machine_state -> Prop) (s : st) (neg : Z) (p d r : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa4 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt5 v8 v16 v24 j0 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (FSL v8 v16 v24 neg s j0 j72) (scopes s) fc m1 ->
      evt psegs Q (S2R E 0x48794 xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 (Z_to_bv 64 (e_off E (k s))) xa4 (Z_to_bv 64 (e_BUF E + p)) xa6 xa7 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xs3 (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 (Z_to_bv 64 (d)) xt5 (Z_to_bv 64 (V8 (B bs r) (B bs (r + 1)) (B bs (r + 2)) (B bs (r + 3)) (B bs (r + 4)) (B bs (r + 5)) (B bs (r + 6)) (B bs (r + 7)))) F fc m1).

  Definition numa_fdig_k (Q : machine_state -> Prop) (s : st) (neg : Z) (p d : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa4 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt5 xt6 v8 v16 v24 j0 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (FSL v8 v16 v24 neg s j0 j72) (scopes s) fc m1 ->
      evt psegs Q (S2R E 0x48800 xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 (Z_to_bv 64 (e_off E (k s))) xa4 (Z_to_bv 64 (e_BUF E + p)) xa6 xa7 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xs3 (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 (Z_to_bv 64 (d)) xt5 xt6 F fc m1).
End NumADefs.
