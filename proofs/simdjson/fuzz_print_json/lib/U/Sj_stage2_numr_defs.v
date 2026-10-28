(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_stage2_defs Sj_stage2_tapek Sj_stage2_numkit Sj_stage2_numkitr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section NumRDefs.
  Variable E : s2env.
  Variables (CP : Z) (t : list Z).

  Definition cp_sep : Prop := (CP + blen t + 64 <= e_TAPE E \/ e_TAPE E + 8 * e_tcap E <= CP)%Z.

  Definition RSL (j0 j8 j16 j24 j32 j72 : list byte) : list cell :=
    [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_IDX E + 4));
     C8 (Z_to_bv 64 (e_SBUF E)); C8 (Z_to_bv 64 (e_THIS E)); CB 8 j72].
  Lemma MEMI_RSL : forall nxt c0 c8 c16 c24 c32 c72 sc fc m1,
    MEMI E nxt [c0; c8; c16; c24; c32; C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_SBUF E)); C8 (Z_to_bv 64 (e_THIS E)); c72] sc fc m1 ->
    csize c0 = 8%nat -> csize c8 = 8%nat -> csize c16 = 8%nat -> csize c24 = 8%nat -> csize c32 = 8%nat -> csize c72 = 8%nat ->
    MEMI E nxt (RSL (cbytes c0) (cbytes c8) (cbytes c16) (cbytes c24) (cbytes c32) (cbytes c72)) sc fc m1.
  Proof.
    intros nxt c0 c8 c16 c24 c32 c72 sc fc m1 H E0 E8 E16 E24 E32 E72. unfold RSL.
    apply (MEMI_forget8 E nxt [] c0 _ sc fc m1 E0) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_] c8 _ sc fc m1 E8) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_; _] c16 _ sc fc m1 E16) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_; _; _] c24 _ sc fc m1 E24) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_; _; _; _] c32 _ sc fc m1 E32) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_; _; _; _; _; _; _; _; _] c72 _ sc fc m1 E72) in H. cbn [app] in H.
    exact H.
  Qed.

  Definition DSL (j0 j8 j16 j24 j32 j56 j72 : list byte) : list cell :=
    [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; C8 (Z_to_bv 64 (e_TAPE E + 8 * 3)); C8 (Z_to_bv 64 (e_IDX E + 4 * 1));
     CB 8 j56; C8 (Z_to_bv 64 (e_THIS E)); CB 8 j72].
  Lemma MEMI_DSL : forall nxt c0 c8 c16 c24 c32 c56 c72 sc fc m1,
    MEMI E nxt [c0; c8; c16; c24; c32; C8 (Z_to_bv 64 (e_TAPE E + 24)); C8 (Z_to_bv 64 (e_IDX E + 4)); c56; C8 (Z_to_bv 64 (e_THIS E)); c72] sc fc m1 ->
    csize c0 = 8%nat -> csize c8 = 8%nat -> csize c16 = 8%nat -> csize c24 = 8%nat -> csize c32 = 8%nat -> csize c56 = 8%nat -> csize c72 = 8%nat ->
    MEMI E nxt (DSL (cbytes c0) (cbytes c8) (cbytes c16) (cbytes c24) (cbytes c32) (cbytes c56) (cbytes c72)) sc fc m1.
  Proof.
    intros nxt c0 c8 c16 c24 c32 c56 c72 sc fc m1 H E0 E8 E16 E24 E32 E56 E72. unfold DSL.
    change (e_IDX E + 4 * 1)%Z with (e_IDX E + 4)%Z. change (e_TAPE E + 8 * 3)%Z with (e_TAPE E + 24)%Z.
    apply (MEMI_forget8 E nxt [] c0 _ sc fc m1 E0) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_] c8 _ sc fc m1 E8) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_; _] c16 _ sc fc m1 E16) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_; _; _] c24 _ sc fc m1 E24) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_; _; _; _] c32 _ sc fc m1 E32) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_; _; _; _; _; _; _] c56 _ sc fc m1 E56) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_; _; _; _; _; _; _; _; _] c72 _ sc fc m1 E72) in H. cbn [app] in H.
    exact H.
  Qed.

  Definition rootnum_k (Q : machine_state -> Prop)  : Prop :=
    forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (RSL j0 j8 j16 j24 j32 j72) [] fc m1 -> bytes_at usegs m1 CP (zbytes (crs t)) ->
      evt usegs Q (S2R E 0x438e4 xra xt0 xt1 xt2 (Z_to_bv 64 (Z.lxor CP 18446744073709551615)) (Z_to_bv 64 (CP)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (e_TAPE E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numr_scan_k (Q : machine_state -> Prop) (neg p e0 x : Z) : Prop :=
    forall xra xt1 xt2 xs0 xa0 xa1 xa2 xa5 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (RSL j0 j8 j16 j24 j32 j72) [] fc m1 -> bytes_at usegs m1 CP (zbytes (crs t)) ->
      evt usegs Q (S2R E 0x44cb0 xra (Z_to_bv 64 (x)) xt1 xt2 xs0 (Z_to_bv 64 (CP)) xa0 xa1 xa2 (Z_to_bv 64 (CP + neg)) (Z_to_bv 64 (CP + p)) xa5 (Z_to_bv 64 (e0)) xa7 xs2 (Z_to_bv 64 (e_TAPE E + 8)) xs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (e_TAPE E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numr_frac_k (Q : machine_state -> Prop) (neg p : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (RSL j0 j8 j16 j24 j32 j72) [] fc m1 -> bytes_at usegs m1 CP (zbytes (crs t)) ->
      evt usegs Q (S2R E 0x43b94 xra xt0 xt1 xt2 xs0 (Z_to_bv 64 (CP)) xa0 xa1 xa2 (Z_to_bv 64 (CP + neg)) (Z_to_bv 64 (CP + p)) xa5 xa6 xa7 xs2 (Z_to_bv 64 (e_TAPE E + 8)) xs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (e_TAPE E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numr_ftail_k (Q : machine_state -> Prop) (neg p d r : Z) : Prop :=
    forall xra xt1 xt2 xs0 xa0 xa1 xa2 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (RSL j0 j8 j16 j24 j32 j72) [] fc m1 -> bytes_at usegs m1 CP (zbytes (crs t)) ->
      evt usegs Q (S2R E 0x44bd4 xra (Z_to_bv 64 (V8 (B (crs t) r) (B (crs t) (r + 1)) (B (crs t) (r + 2)) (B (crs t) (r + 3)) (B (crs t) (r + 4)) (B (crs t) (r + 5)) (B (crs t) (r + 6)) (B (crs t) (r + 7)))) xt1 xt2 xs0 (Z_to_bv 64 (CP)) xa0 xa1 xa2 (Z_to_bv 64 (CP + neg)) (Z_to_bv 64 (CP + p)) xa5 (Z_to_bv 64 (d)) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (e_TAPE E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numr_fdig_k (Q : machine_state -> Prop) (neg p d x : Z) : Prop :=
    forall xra xt1 xt2 xs0 xa0 xa1 xa2 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (RSL j0 j8 j16 j24 j32 j72) [] fc m1 -> bytes_at usegs m1 CP (zbytes (crs t)) ->
      evt usegs Q (S2R E 0x44c48 xra (Z_to_bv 64 (x)) xt1 xt2 xs0 (Z_to_bv 64 (CP)) xa0 xa1 xa2 (Z_to_bv 64 (CP + neg)) (Z_to_bv 64 (CP + p)) xa5 (Z_to_bv 64 (d)) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (e_TAPE E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numr_e48_k (Q : machine_state -> Prop) (neg q0 e0 : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa4 xa5 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (RSL j0 j8 j16 j24 j32 j72) [] fc m1 -> bytes_at usegs m1 CP (zbytes (crs t)) ->
      evt usegs Q (S2R E 0x44cf8 xra xt0 xt1 xt2 xs0 (Z_to_bv 64 (CP)) xa0 xa1 xa2 (Z_to_bv 64 (CP + neg)) xa4 xa5 (Z_to_bv 64 (e0)) (Z_to_bv 64 (CP + q0)) xs2 (Z_to_bv 64 (e_TAPE E + 8)) xs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (e_TAPE E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numr_e14_k (Q : machine_state -> Prop) (neg v e0 x : Z) : Prop :=
    forall xra xt1 xt2 xs0 xa0 xa1 xa2 xa5 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (RSL j0 j8 j16 j24 j32 j72) [] fc m1 -> bytes_at usegs m1 CP (zbytes (crs t)) ->
      evt usegs Q (S2R E 0x44e30 xra (Z_to_bv 64 (x)) xt1 xt2 xs0 (Z_to_bv 64 (CP)) xa0 xa1 xa2 (Z_to_bv 64 (CP + neg)) (Z_to_bv 64 (v)) xa5 (Z_to_bv 64 (e0)) xa7 xs2 (Z_to_bv 64 (e_TAPE E + 8)) xs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (e_TAPE E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numr_eneg_k (Q : machine_state -> Prop) (neg v e0 x : Z) : Prop :=
    forall xra xt1 xt2 xs0 xa0 xa1 xa2 xa5 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (RSL j0 j8 j16 j24 j32 j72) [] fc m1 -> bytes_at usegs m1 CP (zbytes (crs t)) ->
      evt usegs Q (S2R E 0x44e38 xra (Z_to_bv 64 (x)) xt1 xt2 xs0 (Z_to_bv 64 (CP)) xa0 xa1 xa2 (Z_to_bv 64 (CP + neg)) (Z_to_bv 64 (v)) xa5 (Z_to_bv 64 (e0)) xa7 xs2 (Z_to_bv 64 (e_TAPE E + 8)) xs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (e_TAPE E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numr_eadd_k (Q : machine_state -> Prop) (neg w e0 x : Z) : Prop :=
    forall xra xt1 xt2 xs0 xa0 xa1 xa2 xa5 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (RSL j0 j8 j16 j24 j32 j72) [] fc m1 -> bytes_at usegs m1 CP (zbytes (crs t)) ->
      evt usegs Q (S2R E 0x44e4c xra (Z_to_bv 64 (x)) xt1 xt2 xs0 (Z_to_bv 64 (CP)) xa0 xa1 xa2 (Z_to_bv 64 (CP + neg)) (Z_to_bv 64 (w)) xa5 (Z_to_bv 64 (e0)) xa7 xs2 (Z_to_bv 64 (e_TAPE E + 8)) xs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (e_TAPE E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numr_flt_k (Q : machine_state -> Prop) (neg x : Z) : Prop :=
    forall xra xt1 xt2 xs0 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (RSL j0 j8 j16 j24 j32 j72) [] fc m1 -> bytes_at usegs m1 CP (zbytes (crs t)) ->
      evt usegs Q (S2R E 0x44e64 xra (Z_to_bv 64 (x)) xt1 xt2 xs0 (Z_to_bv 64 (CP)) xa0 xa1 xa2 (Z_to_bv 64 (CP + neg)) xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (e_TAPE E + 8)) xs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (e_TAPE E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numr_int_k (Q : machine_state -> Prop) (p : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (RSL j0 j8 j16 j24 j32 j72) [] fc m1 -> bytes_at usegs m1 CP (zbytes (crs t)) ->
      evt usegs Q (S2R E 0x44d5c xra xt0 xt1 xt2 xs0 (Z_to_bv 64 (CP)) xa0 xa1 xa2 xa3 (Z_to_bv 64 (CP + p)) xa5 xa6 xa7 xs2 (Z_to_bv 64 (e_TAPE E + 8)) xs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (e_TAPE E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numr_cmp_k (Q : machine_state -> Prop) (e : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (RSL j0 j8 j16 j24 j32 j72) [] fc m1 -> bytes_at usegs m1 CP (zbytes (crs t)) ->
      evt usegs Q (S2R E 0x459b0 xra xt0 xt1 xt2 xs0 (Z_to_bv 64 (CP)) xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (e)) xa7 xs2 (Z_to_bv 64 (e_TAPE E + 8)) xs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (e_TAPE E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numr_tail_k (Q : machine_state -> Prop) (pc : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (RSL j0 j8 j16 j24 j32 j72) [] fc m1 -> bytes_at usegs m1 CP (zbytes (crs t)) ->
      evt usegs Q (S2R E pc xra xt0 xt1 xt2 xs0 (Z_to_bv 64 (CP)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (e_TAPE E + 8)) xs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (e_TAPE E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition rdel_errA_k (Q : machine_state -> Prop) : Prop :=
    forall xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMX E fc m1 ->
      evt usegs Q (S2R E 0x43990 xra xt0 xt1 xt2 xs0 (Z_to_bv 64 (CP)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition rdel_errB_k (Q : machine_state -> Prop) : Prop :=
    forall code xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      s2_errok E code -> MEMX E fc m1 ->
      evt usegs Q (S2R E 0x46de8 xra xt0 xt1 xt2 (Z_to_bv 64 (code)) (Z_to_bv 64 (CP)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition rdel_fin9_k (Q : machine_state -> Prop) : Prop :=
    forall code xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      (0 < code < 64)%Z -> MEMX E fc m1 ->
      evt usegs Q (S2R E 0x47014 xra xt0 xt1 xt2 (Z_to_bv 64 (code)) (Z_to_bv 64 (CP)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition rdel_fin0_k (Q : machine_state -> Prop) : Prop :=
    forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j56 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (DSL j0 j8 j16 j24 j32 j56 j72) [] fc m1 ->
      evt usegs Q (S2R E 0x47014 xra xt0 xt1 xt2 (Z_to_bv 64 (0)) (Z_to_bv 64 (CP)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).
End NumRDefs.

Ltac r_pose_sep :=
  lazymatch goal with H : cp_sep _ _ _ |- _ => let X := fresh "CPS" in pose proof H as X; unfold cp_sep in X end.
Ltac r_lia := first [ lia0 | s2_pose_sep; lia0 | r_pose_sep; lia0 | r_pose_sep; s2_pose_sep; lia0 ].
Ltac r_tlia := first [ tlia0 | s2_pose_sep; tlia0 | r_pose_sep; tlia0 | r_pose_sep; s2_pose_sep; tlia0 ].
