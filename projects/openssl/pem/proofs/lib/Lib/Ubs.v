(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma ubs_eqb0_false : forall r : word, bv_unsigned r <> 0 -> bv_eqb r (Z_to_bv 64 0) = false.
Proof. intros r H. rewrite bv_eqb_Z. apply Z.eqb_neq. rewrite unsigned_lit by lia. exact H. Qed.

Lemma ubs_eqb0_false_lit : forall x, 0 < x < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = false.
Proof. intros x H. rewrite bv_eqb_Z. apply Z.eqb_neq. rewrite !unsigned_lit by lia. lia. Qed.

Lemma ubs_land_pow2m1 : forall x k, 0 <= k -> x mod 2 ^ k = 0 -> Z.land x (2 ^ k - 1) = 0.
Proof. intros x k Hk H. replace (2 ^ k - 1) with (Z.ones k) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia). rewrite Z.land_ones by lia. exact H. Qed.

Lemma ubs_land3 : forall x, x mod 4 = 0 -> Z.land x 3 = 0.
Proof. intros x H. apply (ubs_land_pow2m1 x 2); [lia | exact H]. Qed.
Lemma ubs_land7 : forall x, x mod 8 = 0 -> Z.land x 7 = 0.
Proof. intros x H. apply (ubs_land_pow2m1 x 3); [lia | exact H]. Qed.
Lemma ubs_land15 : forall x, x mod 16 = 0 -> Z.land x 15 = 0.
Proof. intros x H. apply (ubs_land_pow2m1 x 4); [lia | exact H]. Qed.
Lemma ubs_land1 : forall x, x mod 2 = 0 -> Z.land x 1 = 0.
Proof. intros x H. apply (ubs_land_pow2m1 x 1); [lia | exact H]. Qed.

Lemma ubs_negb_eqb00 : negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) = false.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Ltac ubs_if :=
  try (lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
         lazymatch c with context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by lia end end);
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 0) then _ else _) _ _ _ _) =>
      rewrite (ubs_eqb0_false_lit x) by lia; cbv iota
  | |- evt _ _ (MS _ _ (if bv_eqb ?r (Z_to_bv 64 0) then _ else _) _ _ _ _) =>
      rewrite (ubs_eqb0_false r) by lia; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 (Z.land ?x 3)) (Z_to_bv 64 0)) then _ else _) _ _ _ _) =>
      rewrite (ubs_land3 x) by lia; rewrite ubs_negb_eqb00; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 (Z.land ?x 7)) (Z_to_bv 64 0)) then _ else _) _ _ _ _) =>
      rewrite (ubs_land7 x) by lia; rewrite ubs_negb_eqb00; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 (Z.land ?x 15)) (Z_to_bv 64 0)) then _ else _) _ _ _ _) =>
      rewrite (ubs_land15 x) by lia; rewrite ubs_negb_eqb00; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 (Z.land ?x 1)) (Z_to_bv 64 0)) then _ else _) _ _ _ _) =>
      rewrite (ubs_land1 x) by lia; rewrite ubs_negb_eqb00; cbv iota
  end.
(* [comment removed for export] *)
Ltac ubs_zero_land :=
  repeat match goal with
  | |- context [Z_to_bv 64 (Z.land ?x 3)] => rewrite (ubs_land3 x) by lia
  | |- context [Z_to_bv 64 (Z.land ?x 7)] => rewrite (ubs_land7 x) by lia
  | |- context [Z_to_bv 64 (Z.land ?x 15)] => rewrite (ubs_land15 x) by lia
  end.
