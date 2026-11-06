(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import Floats.SpecFloat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import FP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Open Scope Z_scope.

Definition K_INTMAX : Z := 0x41DFFFFFFFC00000.
Definition K_2P31   : Z := 0x41E0000000000000.
Definition K_INTMIN : Z := 0xC1E0000000000000.
Definition K_M2P31M1 : Z := 0xC1E0000000200000.

Lemma dec_INTMAX : fp_decode fmt_double K_INTMAX = S754_finite false 9007199250546688%positive (-22).
Proof. vm_compute. reflexivity. Qed.
Lemma dec_2P31 : fp_decode fmt_double K_2P31 = S754_finite false 4503599627370496%positive (-21).
Proof. vm_compute. reflexivity. Qed.
Lemma dec_INTMIN : fp_decode fmt_double K_INTMIN = S754_finite true 4503599627370496%positive (-21).
Proof. vm_compute. reflexivity. Qed.
Lemma dec_M2P31M1 : fp_decode fmt_double K_M2P31M1 = S754_finite true 4503599629467648%positive (-21).
Proof. vm_compute. reflexivity. Qed.

Lemma bvu64 : forall x, 0 <= x < 2^64 -> bv_unsigned (Z_to_bv 64 x) = x.
Proof. intros x Hx. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hx. Qed.

(* [comment removed for export] *)
Lemma decode_not_nan : forall x, fp_is_nan fmt_double x = false ->
  match fp_decode fmt_double x with
  | S754_nan => False
  | S754_finite _ _ e => -1074 <= e
  | _ => True
  end.
Proof.
  intros x H. unfold fp_is_nan in H. unfold fp_decode.
  set (e := fp_exp_field fmt_double x) in *. set (m := fp_man_field fmt_double x) in *.
  assert (Hm : 0 <= m). { subst m. unfold fp_man_field. apply Z.land_nonneg. right. change (Z.ones (fp_mw fmt_double)) with (2^52 - 1). lia. }
  destruct (Z.eqb_spec e 0) as [E0|E0].
  - change (fp_emin fmt_double) with (-1074). destruct m; [exact I| lia| exact I].
  - destruct (Z.eqb_spec e (Z.ones (fp_ew fmt_double))) as [E1|E1].
    + destruct (Z.eqb_spec m 0); [exact I| cbn in H; discriminate H].
    + assert (He : 0 <= e). { subst e. unfold fp_exp_field. apply Z.land_nonneg. right. change (Z.ones (fp_ew fmt_double)) with (2^11 - 1). lia. }
      change (Z.shiftl 1 (fp_mw fmt_double)) with (2^52).
      destruct (2^52 + m) eqn:EM; [lia| | lia]. change (fp_emin fmt_double) with (-1074). lia.
Qed.

(* [comment removed for export] *)
Theorem fcast_hi : forall x, 0 <= x < 2^64 -> fp_is_nan fmt_double x = false ->
  fle_d (Z_to_bv 64 K_INTMAX) (Z_to_bv 64 x) = false ->
  flt_d (Z_to_bv 64 x) (Z_to_bv 64 K_2P31) = true.
Proof.
  intros x Hx NN LE. unfold fle_d, flt_d, fp_le, fp_lt, fp_compare in *. cbn [fst] in LE |- *.
  rewrite (bvu64 x), (bvu64 K_INTMAX) in LE by (unfold K_INTMAX; lia).
  rewrite (bvu64 x), (bvu64 K_2P31) by (unfold K_2P31; lia).
  rewrite dec_INTMAX in LE. rewrite dec_2P31.
  pose proof (decode_not_nan x NN) as D.
  destruct (fp_decode fmt_double x) as [sx| sx| |sx mx ex]; cbn [SFcompare] in LE |- *.
  - reflexivity.
  - destruct sx; [reflexivity| discriminate LE].
  - destruct D.
  - destruct sx; [reflexivity|].
    destruct (Z.compare_spec (-22) ex) as [EQ|LT|GT].
    + destruct (Z.compare_spec ex (-21)); try reflexivity; lia.
    + discriminate LE.
    + destruct (Z.compare_spec ex (-21)); try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Theorem fcast_lo : forall x, 0 <= x < 2^64 -> fp_is_nan fmt_double x = false ->
  fle_d (Z_to_bv 64 x) (Z_to_bv 64 K_INTMIN) = false ->
  flt_d (Z_to_bv 64 K_M2P31M1) (Z_to_bv 64 x) = true.
Proof.
  intros x Hx NN LE. unfold fle_d, flt_d, fp_le, fp_lt, fp_compare in *. cbn [fst] in LE |- *.
  rewrite (bvu64 x), (bvu64 K_INTMIN) in LE by (unfold K_INTMIN; lia).
  rewrite (bvu64 x), (bvu64 K_M2P31M1) by (unfold K_M2P31M1; lia).
  rewrite dec_INTMIN in LE. rewrite dec_M2P31M1.
  pose proof (decode_not_nan x NN) as D.
  destruct (fp_decode fmt_double x) as [sx| sx| |sx mx ex]; cbn [SFcompare] in LE |- *.
  - reflexivity.
  - destruct sx; [discriminate LE| reflexivity].
  - destruct D.
  - destruct sx; [| reflexivity].
    rewrite !Pos.compare_cont_spec in LE |- *.
    destruct (Z.compare_spec ex (-21)) as [EQ|LT|GT].
    + subst ex. rewrite Z.compare_refl.
      destruct (Pos.compare_spec mx 4503599627370496) as [E|L|G]; try discriminate LE.
      destruct (Pos.compare_spec 4503599629467648 mx) as [E'|L'|G']; try reflexivity; exfalso.
      * rewrite <- E' in L. apply Pos2Z.pos_lt_pos in L. cbn in L. lia.
      * apply Pos2Z.pos_lt_pos in L. apply Pos2Z.pos_lt_pos in L'. lia.
    + replace (-21 ?= ex)%Z with Gt by (symmetry; apply Z.compare_gt_iff; lia). reflexivity.
    + discriminate LE.
Qed.
