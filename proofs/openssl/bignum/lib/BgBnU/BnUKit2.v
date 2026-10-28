(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr ZBridge.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma land7_mod64 : forall e, Z.land (bv_unsigned (Z_to_bv 64 e)) 7 = Z.land e 7.
Proof.
  intros e. change 7 with (Z.ones 3). rewrite !Z.land_ones by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma lor_land7 : forall x y, x mod 8 = 0 -> y mod 8 = 0 ->
  Z.land (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 x)) (bv_unsigned (Z_to_bv 64 y))))) 7 = 0.
Proof. intros x y Hx Hy. rewrite land7_mod64, Z.land_lor_distr_l, !land7_wrap by assumption. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sltu_ge : forall x y, 0 <= y <= x -> x < 2^64 -> v_sltu (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 0.
Proof.
  intros x y H1 H2. rewrite v_sltu_b2z. rewrite !unsigned_lit by lia. replace (x <? y) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
Lemma sltu_lt : forall x y, 0 <= x < y -> y < 2^64 -> v_sltu (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 1.
Proof.
  intros x y H1 H2. rewrite v_sltu_b2z. rewrite !unsigned_lit by lia. replace (x <? y) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
