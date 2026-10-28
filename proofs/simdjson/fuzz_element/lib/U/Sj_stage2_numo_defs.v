(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_defs Sj_stage2_tapek Sj_stage2_numkit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section NumODefs.
  Variable E : s2env.
  Notation bs := (e_bs E).

  Definition NSL (s : st) (neg Wv : Z) (j0 j8 j16 j24 j72 : list byte) : list cell :=
    [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; C8 (Z_to_bv 64 (depth s)); C8 (Z_to_bv 64 (e_TAPE E + 8 * Wv));
     C8 (Z_to_bv 64 neg); C8 (Z_to_bv 64 (e_SBUF E + sb s)); C8 (Z_to_bv 64 (e_THIS E)); CB 8 j72].

  Lemma MEMI_NSL : forall nxt s neg Wv c0 c8 c16 c24 c72 sc fc m1,
    MEMI E nxt [c0; c8; c16; c24; C8 (Z_to_bv 64 (depth s)); C8 (Z_to_bv 64 (e_TAPE E + 8 * Wv)); C8 (Z_to_bv 64 neg);
                C8 (Z_to_bv 64 (e_SBUF E + sb s)); C8 (Z_to_bv 64 (e_THIS E)); c72] sc fc m1 ->
    csize c0 = 8%nat -> csize c8 = 8%nat -> csize c16 = 8%nat -> csize c24 = 8%nat -> csize c72 = 8%nat ->
    MEMI E nxt (NSL s neg Wv (cbytes c0) (cbytes c8) (cbytes c16) (cbytes c24) (cbytes c72)) sc fc m1.
  Proof.
    intros nxt s neg Wv c0 c8 c16 c24 c72 sc fc m1 H E0 E8 E16 E24 E72. unfold NSL.
    apply (MEMI_forget8 E nxt [] c0 _ sc fc m1 E0) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_] c8 _ sc fc m1 E8) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_; _] c16 _ sc fc m1 E16) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_; _; _] c24 _ sc fc m1 E24) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_; _; _; _; _; _; _; _; _] c72 _ sc fc m1 E72) in H. cbn [app] in H.
    exact H.
  Qed.

  Definition numo_scan_k (Q : machine_state -> Prop) (s : st) (neg : Z) (p e0 x : Z) : Prop :=
    forall xra xt0 xt2 xs0 xa0 xa1 xa2 xa3 xa6 xs2 xs3 xs4 xs6 xs7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (NSL s neg (W s) j0 j8 j16 j24 j72) (scopes s) fc m1 ->
      evt usegs Q (S2R E 0x4b764 xra xt0 (Z_to_bv 64 (x)) xt2 xs0 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xa0 xa1 xa2 xa3 (Z_to_bv 64 (e_BUF E + (e_off E (k s) + neg))) (Z_to_bv 64 (e_BUF E + p)) xa6 (Z_to_bv 64 (e0)) xs2 xs3 xs4 (Z_to_bv 64 (e_BUF E)) xs6 xs7 xs8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))) xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numo_frac_k (Q : machine_state -> Prop) (s : st) (neg : Z) (p : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa6 xa7 xs2 xs3 xs4 xs6 xs7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (NSL s neg (W s) j0 j8 j16 j24 j72) (scopes s) fc m1 ->
      evt usegs Q (S2R E 0x4b2cc xra xt0 xt1 xt2 xs0 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xa0 xa1 xa2 xa3 (Z_to_bv 64 (e_BUF E + (e_off E (k s) + neg))) (Z_to_bv 64 (e_BUF E + p)) xa6 xa7 xs2 xs3 xs4 (Z_to_bv 64 (e_BUF E)) xs6 xs7 xs8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))) xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numo_ftail_k (Q : machine_state -> Prop) (s : st) (neg : Z) (p d r : Z) : Prop :=
    forall xra xt0 xt2 xs0 xa0 xa1 xa2 xa3 xa6 xs2 xs3 xs4 xs6 xs7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (NSL s neg (W s) j0 j8 j16 j24 j72) (scopes s) fc m1 ->
      evt usegs Q (S2R E 0x4b474 xra xt0 (Z_to_bv 64 (V8 (B bs r) (B bs (r + 1)) (B bs (r + 2)) (B bs (r + 3)) (B bs (r + 4)) (B bs (r + 5)) (B bs (r + 6)) (B bs (r + 7)))) xt2 xs0 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xa0 xa1 xa2 xa3 (Z_to_bv 64 (e_BUF E + (e_off E (k s) + neg))) (Z_to_bv 64 (e_BUF E + p)) xa6 (Z_to_bv 64 (d)) xs2 xs3 xs4 (Z_to_bv 64 (e_BUF E)) xs6 xs7 xs8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))) xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numo_fdig_k (Q : machine_state -> Prop) (s : st) (neg : Z) (p d x : Z) : Prop :=
    forall xra xt0 xt2 xs0 xa0 xa1 xa2 xa3 xa6 xs2 xs3 xs4 xs6 xs7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (NSL s neg (W s) j0 j8 j16 j24 j72) (scopes s) fc m1 ->
      evt usegs Q (S2R E 0x4b4e8 xra xt0 (Z_to_bv 64 (x)) xt2 xs0 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xa0 xa1 xa2 xa3 (Z_to_bv 64 (e_BUF E + (e_off E (k s) + neg))) (Z_to_bv 64 (e_BUF E + p)) xa6 (Z_to_bv 64 (d)) xs2 xs3 xs4 (Z_to_bv 64 (e_BUF E)) xs6 xs7 xs8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))) xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numo_e48_k (Q : machine_state -> Prop) (s : st) (neg : Z) (q0 e0 : Z) : Prop :=
    forall xra xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa5 xa6 xs2 xs3 xs4 xs6 xs7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (NSL s neg (W s) j0 j8 j16 j24 j72) (scopes s) fc m1 ->
      evt usegs Q (S2R E 0x4b7a4 xra (Z_to_bv 64 (e_BUF E + q0)) xt1 xt2 xs0 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xa0 xa1 xa2 xa3 (Z_to_bv 64 (e_BUF E + (e_off E (k s) + neg))) xa5 xa6 (Z_to_bv 64 (e0)) xs2 xs3 xs4 (Z_to_bv 64 (e_BUF E)) xs6 xs7 xs8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))) xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numo_flt_k (Q : machine_state -> Prop) (s : st) (neg : Z) (x : Z) : Prop :=
    forall xra xt0 xt2 xs0 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs2 xs3 xs4 xs6 xs7 xs8 xs10 xs11 xt4 xt5 xt6 j0 j8 j16 j24 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (NSL s neg (W s) j0 j8 j16 j24 j72) (scopes s) fc m1 ->
      evt usegs Q (S2R E 0x4b858 xra xt0 (Z_to_bv 64 (x)) xt2 xs0 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xa0 xa1 xa2 xa3 (Z_to_bv 64 (e_BUF E + (e_off E (k s) + neg))) xa5 xa6 xa7 xs2 xs3 xs4 (Z_to_bv 64 (e_BUF E)) xs6 xs7 xs8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))) xs10 xs11 (Z_to_bv 64 (e_TAPE E + 8 * W s)) xt4 xt5 xt6 F fc m1).

  Definition numo_int_k (Q : machine_state -> Prop) (s : st) (neg : Z) (p : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa6 xa7 xs2 xs3 xs4 xs6 xs7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (NSL s neg (W s) j0 j8 j16 j24 j72) (scopes s) fc m1 ->
      evt usegs Q (S2R E 0x4bb0c xra xt0 xt1 xt2 xs0 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xa0 xa1 xa2 xa3 xa4 (Z_to_bv 64 (e_BUF E + p)) xa6 xa7 xs2 xs3 xs4 (Z_to_bv 64 (e_BUF E)) xs6 xs7 xs8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))) xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numo_cmp_k (Q : machine_state -> Prop) (s : st) (neg : Z) (e : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs2 xs3 xs4 xs6 xs7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (NSL s neg (W s) j0 j8 j16 j24 j72) (scopes s) fc m1 ->
      evt usegs Q (S2R E 0x4b964 xra xt0 xt1 xt2 xs0 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xa0 xa1 xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 (e)) xs2 xs3 xs4 (Z_to_bv 64 (e_BUF E)) xs6 xs7 xs8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))) xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numo_tail_k (Q : machine_state -> Prop) (s : st) (neg : Z) (pc : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs6 xs7 xs8 xs10 xs11 xt4 xt5 xt6 j0 j8 j16 j24 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (NSL s neg (W s) j0 j8 j16 j24 j72) (scopes s) fc m1 ->
      evt usegs Q (S2R E pc xra xt0 xt1 xt2 xs0 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 (Z_to_bv 64 (e_BUF E)) xs6 xs7 xs8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))) xs10 xs11 (Z_to_bv 64 (e_TAPE E + 8 * W s)) xt4 xt5 xt6 F fc m1).

  Definition numo_tailm_k (Q : machine_state -> Prop) (s : st) (neg : Z) (pc : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs6 xs7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (NSL s neg (W s) j0 j8 j16 j24 j72) (scopes s) fc m1 ->
      evt usegs Q (S2R E pc xra xt0 xt1 xt2 xs0 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 (Z_to_bv 64 (e_BUF E)) xs6 xs7 xs8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))) xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).
End NumODefs.
