(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Musl Require Import MuslStr.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzArrD. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem CmpFsKit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCLemmasMs CmpMsKit.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLia.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Lemma bvlts0l_true : forall x, - 9223372036854775808 <= x < 9223372036854775808 ->
  bv_lts (Z_to_bv 64 0) (Z_to_bv 64 x) = true -> 0 < x.
Proof.
  intros x Hx H. unfold bv_lts in H. apply Z.ltb_lt in H. rewrite signed_lit_small, signed_lit_small in H by lia. exact H.
Qed.
Lemma bvlts0l_false : forall x, - 9223372036854775808 <= x < 9223372036854775808 ->
  bv_lts (Z_to_bv 64 0) (Z_to_bv 64 x) = false -> x <= 0.
Proof.
  intros x Hx H. unfold bv_lts in H. apply Z.ltb_ge in H. rewrite signed_lit_small, signed_lit_small in H by lia. lia.
Qed.
Lemma blez_taken : forall x, - 9223372036854775808 <= x < 9223372036854775808 ->
  negb (bv_lts (Z_to_bv 64 0) (Z_to_bv 64 x)) = true -> x <= 0.
Proof. intros x Hx H. apply (bvlts0l_false x Hx). destruct (bv_lts _ _); [discriminate| reflexivity]. Qed.
Lemma blez_not_taken : forall x, - 9223372036854775808 <= x < 9223372036854775808 ->
  negb (bv_lts (Z_to_bv 64 0) (Z_to_bv 64 x)) = false -> 0 < x.
Proof. intros x Hx H. apply (bvlts0l_true x Hx). destruct (bv_lts _ _); [reflexivity| discriminate]. Qed.
Lemma bgtz_taken : forall x, - 9223372036854775808 <= x < 9223372036854775808 ->
  bv_lts (Z_to_bv 64 0) (Z_to_bv 64 x) = true -> 0 < x.
Proof. exact bvlts0l_true. Qed.
Lemma bgtz_not_taken : forall x, - 9223372036854775808 <= x < 9223372036854775808 ->
  bv_lts (Z_to_bv 64 0) (Z_to_bv 64 x) = false -> x <= 0.
Proof. exact bvlts0l_false. Qed.

(* [comment removed for export] *)
Lemma land_dbl_m4 : forall x, (0 <= x < 4611686018427387904)%Z -> Z.land (x * 2) 18446744073709551612 = (4 * (x / 2))%Z.
Proof.
  intros x Hx. change 18446744073709551612%Z with (2^64 - 2^2)%Z. rewrite land_align_down by lia.
  change (2 ^ 2)%Z with 4%Z. Z.div_mod_to_equations. lia.
Qed.

Lemma swrap32_unsigned_sub : forall a b, bv_swrap 32 (bv_unsigned (Z_to_bv 64 a) - b) = bv_swrap 32 (a - b).
Proof.
  intros. apply swrap32_eqm. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with (18446744073709551616)%Z. change (2^32)%Z with 4294967296%Z.
  Z.div_mod_to_equations. lia.
Qed.


Lemma land_CM64 : forall x, (0 <= x < 4294967296)%Z -> Z.land x 18446744073707454463 = clearmask x.
Proof.
  intros x Hx. unfold clearmask.
  change 18446744073707454463%Z with (Z.lor 4292870143 (Z.shiftl 4294967295 32)).
  rewrite Z.land_lor_distr_r.
  replace (Z.land x (Z.shiftl 4294967295 32)) with 0%Z; [rewrite Z.lor_0_r; reflexivity|].
  symmetry. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.ltb_spec k 32).
  - rewrite Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
  - rewrite (Z.bits_above_log2 x k); [reflexivity| lia|].
    destruct (Z.eq_dec x 0) as [->|NZ]; [cbn; lia|].
    assert (Z.log2 x < 32)%Z by (apply Z.log2_lt_pow2; lia). lia.
Qed.

Lemma signed_lit_high : forall z, (2^63 <= z < 2^64)%Z -> bv_signed (Z_to_bv 64 z) = (z - 2^64)%Z.
Proof.
  intros z Hz. unfold bv_signed. rewrite Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with (2^64)%Z. change (2 ^ 64 `div` 2)%Z with (2^63)%Z.
  rewrite Z.add_mod_idemp_l by lia. Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
Lemma slt42_true : forall x, (0 <= x < 4194304)%Z -> bv_lts (Z_to_bv 64 (x * 4398046511104)) (Z_to_bv 64 0) = true -> (2097152 <= x)%Z.
Proof.
  intros x Hx H. unfold bv_lts in H. apply Z.ltb_lt in H. rewrite (signed_lit_small 0) in H by lia.
  destruct (Z.lt_ge_cases x 2097152); [|assumption]. rewrite signed_lit_small in H by lia. lia.
Qed.
Lemma slt42_false : forall x, (0 <= x < 4194304)%Z -> bv_lts (Z_to_bv 64 (x * 4398046511104)) (Z_to_bv 64 0) = false -> (x < 2097152)%Z.
Proof.
  intros x Hx H. unfold bv_lts in H. apply Z.ltb_ge in H. rewrite (signed_lit_small 0) in H by lia.
  destruct (Z.lt_ge_cases x 2097152); [assumption|]. rewrite signed_lit_high in H by lia. lia.
Qed.


Lemma bveqb_lit_false : forall x y, bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = false ->
  (x mod 18446744073709551616 <> y mod 18446744073709551616)%Z.
Proof.
  intros x y H. unfold bv_eqb in H. apply Z.eqb_neq in H. rewrite !Z_to_bv_unsigned in H.
  unfold bv_wrap, bv_modulus in H. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in H. exact H.
Qed.
(* [comment removed for export] *)


End ACeilS1.
