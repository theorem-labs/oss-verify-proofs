(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZChkAdl.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZChkAdl.ZChkArith.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Set Warnings "-abstract-large-number".
Definition AMAG : Z := 4223091239536077.

Section Walk.
Variable P : Z.
Hypothesis HP0 : 0 <= P.


Definition NMX : nat := 5552.
Lemma Z_of_nat_NMX : Z.of_nat NMX = 5552.
Proof. reflexivity. Qed.


Lemma land_m16 : forall a, Z.land a (-16) = a / 16 * 16.
Proof.
  intros a. change (-16) with (Z.lnot (Z.ones 4)).
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma land_15 : forall a, Z.land a 15 = a mod 16.
Proof. intros a. change 15 with (Z.ones 4). apply Z.land_ones. lia. Qed.


Lemma eqm_refl : forall x, eqm x x.
Proof. intro x. reflexivity. Qed.

End Walk.

