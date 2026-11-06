(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Sj_stage2_defs Sj_stage2_numkit Sj_stage2_numkit3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section NumRDefs.
  Variable E : s2env.
  Variables (CP : Z) (t : list Z).

  Definition cp_sep : Prop := (CP + blen t + 64 <= e_TAPE E \/ e_TAPE E + 8 * e_tcap E <= CP)%Z.

  Definition RSL (j0 j8 j16 j24 j32 j40 j72 : list byte) : list cell :=
    [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; C8 (Z_to_bv 64 (e_IDX E + 4));
     C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_SBUF E)); CB 8 j72].

  Lemma MEMI_RSL : forall nxt c0 c8 c16 c24 c32 c40 c72 sc fc m1,
    MEMI E nxt [c0; c8; c16; c24; c32; c40; C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_SBUF E)); c72] sc fc m1 ->
    csize c0 = 8%nat -> csize c8 = 8%nat -> csize c16 = 8%nat -> csize c24 = 8%nat -> csize c32 = 8%nat -> csize c40 = 8%nat -> csize c72 = 8%nat ->
    MEMI E nxt (RSL (cbytes c0) (cbytes c8) (cbytes c16) (cbytes c24) (cbytes c32) (cbytes c40) (cbytes c72)) sc fc m1.
  Proof.
    intros nxt c0 c8 c16 c24 c32 c40 c72 sc fc m1 H E0 E8 E16 E24 E32 E40 E72. unfold RSL.
    apply (MEMI_forget8 E nxt [] c0 _ sc fc m1 E0) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_] c8 _ sc fc m1 E8) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_; _] c16 _ sc fc m1 E16) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_; _; _] c24 _ sc fc m1 E24) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_; _; _; _] c32 _ sc fc m1 E32) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_; _; _; _; _] c40 _ sc fc m1 E40) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_; _; _; _; _; _; _; _; _] c72 _ sc fc m1 E72) in H. cbn [app] in H.
    exact H.
  Qed.

  Definition RFSL (v32 : word) (neg : Z) (j0 j8 j16 j24 j72 : list byte) : list cell :=
    [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; C8 v32; C8 (Z_to_bv 64 neg); C8 (Z_to_bv 64 (e_IDX E + 4));
     C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_SBUF E)); CB 8 j72].

  Definition DSL (j0 j1 j2 j3 j4 j5 j8 j9 : list byte) : list cell :=
    [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; C8 (Z_to_bv 64 (e_IDX E + 4 * 1));
     C8 (Z_to_bv 64 (e_TAPE E + 8 * 3)); CB 8 j8; CB 8 j9].
  Lemma MEMI_DSL : forall nxt c0 c1 c2 c3 c4 c5 c8 c9 sc fc m1,
    MEMI E nxt [c0; c1; c2; c3; c4; c5; C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_TAPE E + 24)); c8; c9] sc fc m1 ->
    csize c0 = 8%nat -> csize c1 = 8%nat -> csize c2 = 8%nat -> csize c3 = 8%nat -> csize c4 = 8%nat -> csize c5 = 8%nat ->
    csize c8 = 8%nat -> csize c9 = 8%nat ->
    MEMI E nxt (DSL (cbytes c0) (cbytes c1) (cbytes c2) (cbytes c3) (cbytes c4) (cbytes c5) (cbytes c8) (cbytes c9)) sc fc m1.
  Proof.
    intros nxt c0 c1 c2 c3 c4 c5 c8 c9 sc fc m1 H E0 E1 E2 E3 E4 E5 E8 E9. unfold DSL.
    change (e_IDX E + 4 * 1)%Z with (e_IDX E + 4)%Z. change (e_TAPE E + 8 * 3)%Z with (e_TAPE E + 24)%Z.
    apply (MEMI_forget8 E nxt [] c0 _ sc fc m1 E0) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_] c1 _ sc fc m1 E1) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_; _] c2 _ sc fc m1 E2) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_; _; _] c3 _ sc fc m1 E3) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_; _; _; _] c4 _ sc fc m1 E4) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_; _; _; _; _] c5 _ sc fc m1 E5) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_; _; _; _; _; _; _; _] c8 _ sc fc m1 E8) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_; _; _; _; _; _; _; _; _] c9 _ sc fc m1 E9) in H. cbn [app] in H.
    exact H.
  Qed.

  Definition rootnum_k (Q : machine_state -> Prop)  : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j40 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (RSL j0 j8 j16 j24 j32 j40 j72) [] fc m1 -> bytes_at psegs m1 CP (zbytes (crs t)) ->
      evt psegs Q (S2R E 0x3dc54 xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (CP)) xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 (e_TAPE E)) xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numr_scan_k (Q : machine_state -> Prop) (neg p : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 xt4 xt6 j0 j8 j16 j24 j32 j40 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (RSL j0 j8 j16 j24 j32 j40 j72) [] fc m1 -> bytes_at psegs m1 CP (zbytes (crs t)) ->
      evt psegs Q (S2R E 0x3ea08 xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 xa3 (Z_to_bv 64 (CP + p)) xa5 xa6 xa7 (Z_to_bv 64 (CP)) xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 (e_TAPE E)) xs9 xs10 xs11 (Z_to_bv 64 (B (crs t) p)) xt4 (Z_to_bv 64 (neg)) xt6 F fc m1).

  Definition numr_frac_k (Q : machine_state -> Prop) (neg p : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt4 xt6 j0 j8 j16 j24 j32 j40 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (RSL j0 j8 j16 j24 j32 j40 j72) [] fc m1 -> bytes_at psegs m1 CP (zbytes (crs t)) ->
      evt psegs Q (S2R E 0x3dfe8 xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 xa3 (Z_to_bv 64 (CP + p)) xa5 xa6 xa7 (Z_to_bv 64 (CP)) xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 (e_TAPE E)) xs9 xs10 xs11 xt3 xt4 (Z_to_bv 64 (neg)) xt6 F fc m1).

  Definition numr_flt_k (Q : machine_state -> Prop) (neg c : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 xt4 xt6 j0 j8 j16 j24 j32 j40 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (RSL j0 j8 j16 j24 j32 j40 j72) [] fc m1 -> bytes_at psegs m1 CP (zbytes (crs t)) ->
      evt psegs Q (S2R E 0x3f08c xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (CP)) xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 (e_TAPE E)) xs9 xs10 xs11 (Z_to_bv 64 (c)) xt4 (Z_to_bv 64 (neg)) xt6 F fc m1).

  Definition numr_int_k (Q : machine_state -> Prop) (p : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j40 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (RSL j0 j8 j16 j24 j32 j40 j72) [] fc m1 -> bytes_at psegs m1 CP (zbytes (crs t)) ->
      evt psegs Q (S2R E 0x3ea3c xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 xa3 (Z_to_bv 64 (CP + p)) xa5 xa6 xa7 (Z_to_bv 64 (CP)) xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 (e_TAPE E)) xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numr_e48_k (Q : machine_state -> Prop) (neg q0 : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt4 xt6 j0 j8 j16 j24 j32 j40 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (RSL j0 j8 j16 j24 j32 j40 j72) [] fc m1 -> bytes_at psegs m1 CP (zbytes (crs t)) ->
      evt psegs Q (S2R E 0x3f02c xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (CP + q0)) (Z_to_bv 64 (B (crs t) q0)) (Z_to_bv 64 (CP)) xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 (e_TAPE E)) xs9 xs10 xs11 xt3 xt4 (Z_to_bv 64 (neg)) xt6 F fc m1).

  Definition numr_e78_k (Q : machine_state -> Prop) (neg c : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 xt4 xt6 j0 j8 j16 j24 j32 j40 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (RSL j0 j8 j16 j24 j32 j40 j72) [] fc m1 -> bytes_at psegs m1 CP (zbytes (crs t)) ->
      evt psegs Q (S2R E 0x3f07c xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (CP)) xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 (e_TAPE E)) xs9 xs10 xs11 (Z_to_bv 64 (c)) xt4 (Z_to_bv 64 (neg)) xt6 F fc m1).

  Definition numr_cmp_k (Q : machine_state -> Prop) (e : Z) : Prop :=
    forall xra xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j40 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (RSL j0 j8 j16 j24 j32 j40 j72) [] fc m1 -> bytes_at psegs m1 CP (zbytes (crs t)) ->
      evt psegs Q (S2R E 0x3f9bc xra (Z_to_bv 64 (e)) xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (CP)) xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 (e_TAPE E)) xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numr_tail_k (Q : machine_state -> Prop) (pc : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j40 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (RSL j0 j8 j16 j24 j32 j40 j72) [] fc m1 -> bytes_at psegs m1 CP (zbytes (crs t)) ->
      evt psegs Q (S2R E pc xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (CP)) xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 (e_TAPE E)) xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numr_wr_k (Q : machine_state -> Prop) : Prop :=
    forall s1v xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j40 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      (s1v = 0 \/ s1v = 9)%Z ->
      MEMI E (e_nxt0 E) (RSL j0 j8 j16 j24 j32 j40 j72) [] fc m1 -> bytes_at psegs m1 CP (zbytes (crs t)) ->
      evt psegs Q (S2R E 0x400fc xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 s1v) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (CP)) xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 (e_TAPE E)) xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numr_ftail_k (Q : machine_state -> Prop) (neg p d r : Z) : Prop :=
    forall xra xt0 xt1 xs1 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 xt4 xt5 xt6 v32 j0 j8 j16 j24 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (RFSL v32 neg j0 j8 j16 j24 j72) [] fc m1 -> bytes_at psegs m1 CP (zbytes (crs t)) ->
      evt psegs Q (S2R E 0x3e934 xra xt0 xt1 (Z_to_bv 64 (d)) (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 xa3 (Z_to_bv 64 (CP + p)) xa5 xa6 xa7 (Z_to_bv 64 (CP)) xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 (e_TAPE E)) xs9 xs10 xs11 (Z_to_bv 64 (V8 (B (crs t) r) (B (crs t) (r + 1)) (B (crs t) (r + 2)) (B (crs t) (r + 3)) (B (crs t) (r + 4)) (B (crs t) (r + 5)) (B (crs t) (r + 6)) (B (crs t) (r + 7)))) xt4 xt5 xt6 F fc m1).

  Definition numr_fdig_k (Q : machine_state -> Prop) (neg p d : Z) : Prop :=
    forall xra xt0 xt1 xs1 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 v32 j0 j8 j16 j24 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (RFSL v32 neg j0 j8 j16 j24 j72) [] fc m1 -> bytes_at psegs m1 CP (zbytes (crs t)) ->
      evt psegs Q (S2R E 0x3e9a0 xra xt0 xt1 (Z_to_bv 64 (d)) (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 xa3 (Z_to_bv 64 (CP + p)) xa5 xa6 xa7 (Z_to_bv 64 (CP)) xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 (e_TAPE E)) xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition rdel_err_k (Q : machine_state -> Prop) : Prop :=
    forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMX E fc m1 -> s2_fail xs1 ->
      evt psegs Q (S2R E 0x3ddec xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (CP)) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition rdel_int_k (Q : machine_state -> Prop) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j0 j1 j2 j3 j4 j5 j8 j9 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (DSL j0 j1 j2 j3 j4 j5 j8 j9) [] fc m1 ->
      evt psegs Q (S2R E 0x3ffbc xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (CP)) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition rdel_flt0_k (Q : machine_state -> Prop) : Prop :=
    forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j0 j1 j2 j3 j4 j5 j8 j9 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (DSL j0 j1 j2 j3 j4 j5 j8 j9) [] fc m1 ->
      evt psegs Q (S2R E 0x403e8 xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (0)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (CP)) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition rdel_flt9_k (Q : machine_state -> Prop) : Prop :=
    forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      s2_fail xs1 -> MEMX E fc m1 ->
      evt psegs Q (S2R E 0x403e8 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (CP)) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).
End NumRDefs.

Ltac r_pose_sep :=
  lazymatch goal with H : cp_sep _ _ _ |- _ => let X := fresh "CPS" in pose proof H as X; unfold cp_sep in X end.
Ltac r_lia := first [ lia0 | s2_pose_sep; lia0 | r_pose_sep; lia0 | r_pose_sep; s2_pose_sep; lia0 ].
Ltac r_tlia := first [ tlia0 | s2_pose_sep; tlia0 | r_pose_sep; tlia0 | r_pose_sep; s2_pose_sep; tlia0 ].
