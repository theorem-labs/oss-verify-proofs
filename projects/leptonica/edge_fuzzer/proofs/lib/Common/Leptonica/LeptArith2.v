(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition sw32 (z : Z) : Z := (z + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31.
Definition zx (z : Z) : Z := z mod 2 ^ 64.

Lemma sw32_eq : forall z, bv_swrap 32 z = sw32 z.
Proof. intros z. reflexivity. Qed.

Lemma sw32_range : forall z, - 2 ^ 31 <= sw32 z < 2 ^ 31.
Proof. intros z. unfold sw32. pose proof (Z.mod_pos_bound (z + 2 ^ 31) (2 ^ 32) ltac:(lia)). lia. Qed.

Lemma sw32_small : forall z, - 2 ^ 31 <= z < 2 ^ 31 -> sw32 z = z.
Proof. intros z Hz. unfold sw32. rewrite Z.mod_small by lia. lia. Qed.

Lemma sw32_mod : forall z k, sw32 (z + 2 ^ 32 * k) = sw32 z.
Proof.
  intros z k. unfold sw32. f_equal. replace (z + 2 ^ 32 * k + 2 ^ 31) with (z + 2 ^ 31 + k * 2 ^ 32) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma zx_range : forall z, 0 <= zx z < 2 ^ 64.
Proof. intros z. unfold zx. apply Z.mod_pos_bound. lia. Qed.

Lemma zx_small : forall z, 0 <= z < 2 ^ 64 -> zx z = z.
Proof. intros z Hz. unfold zx. apply Z.mod_small. lia. Qed.

Lemma zx_neg : forall z, - 2 ^ 64 <= z < 0 -> zx z = z + 2 ^ 64.
Proof.
  intros z Hz. unfold zx. replace z with ((z + 2 ^ 64) + (-1) * 2 ^ 64) at 1 by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma zbv_zx : forall z, Z_to_bv 64 (zx z) = Z_to_bv 64 z.
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold zx, bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma u_zbv : forall z, bv_unsigned (Z_to_bv 64 z) = zx z.
Proof. intros z. rewrite Z_to_bv_unsigned. reflexivity. Qed.

(* [comment removed for export] *)
Lemma v_lw_Z : forall z, v_lw (Z_to_bv 64 z) = Z_to_bv 64 (sw32 z).
Proof.
  intros z. unfold v_lw. rewrite u_zbv, sw32_eq. unfold zx.
  rewrite <- (sw32_mod (z mod 2 ^ 64) ((z / 2 ^ 64) * 2 ^ 32)). f_equal. f_equal.
  pose proof (Z.div_mod z (2 ^ 64) ltac:(lia)). lia.
Qed.

Lemma v_addw_Z : forall a b, v_addw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (sw32 (a + b)).
Proof.
  intros a b. unfold v_addw. rewrite !u_zbv, sw32_eq. unfold zx. f_equal.
  rewrite <- (sw32_mod (a mod 2 ^ 64 + b mod 2 ^ 64) ((a / 2 ^ 64 + b / 2 ^ 64) * 2 ^ 32)). f_equal.
  pose proof (Z.div_mod a (2 ^ 64) ltac:(lia)). pose proof (Z.div_mod b (2 ^ 64) ltac:(lia)). lia.
Qed.

Lemma v_subw_Z : forall a b, v_subw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (sw32 (a - b)).
Proof.
  intros a b. unfold v_subw. rewrite !u_zbv, sw32_eq. unfold zx. f_equal.
  rewrite <- (sw32_mod (a mod 2 ^ 64 - b mod 2 ^ 64) ((a / 2 ^ 64 - b / 2 ^ 64) * 2 ^ 32)). f_equal.
  pose proof (Z.div_mod a (2 ^ 64) ltac:(lia)). pose proof (Z.div_mod b (2 ^ 64) ltac:(lia)). lia.
Qed.

Lemma v_addiw_Z : forall a i, v_addiw (Z_to_bv 64 a) i = Z_to_bv 64 (sw32 (a + i)).
Proof.
  intros a i. unfold v_addiw. rewrite u_zbv, sw32_eq. unfold zx. f_equal.
  rewrite <- (sw32_mod (a mod 2 ^ 64 + i) ((a / 2 ^ 64) * 2 ^ 32)). f_equal.
  pose proof (Z.div_mod a (2 ^ 64) ltac:(lia)). lia.
Qed.

Lemma v_slliw_2 : forall a, v_slliw (Z_to_bv 64 a) 2 = Z_to_bv 64 (sw32 (a * 4)).
Proof.
  intros a. unfold v_slliw. rewrite u_zbv, sw32_eq, Z.shiftl_mul_pow2 by lia. unfold zx. f_equal. change (2 ^ 2) with 4.
  rewrite <- (sw32_mod (a mod 2 ^ 64 * 4) ((a / 2 ^ 64) * 2 ^ 34)). f_equal.
  pose proof (Z.div_mod a (2 ^ 64) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma c_ltu_zx : forall a b, c_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (zx a <? zx b).
Proof. intros a b. unfold c_ltu, bv_ltu. rewrite !u_zbv. reflexivity. Qed.

Lemma c_eq_zx : forall a b, c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = (zx a =? zx b).
Proof. intros a b. unfold c_eq, bv_eqb. rewrite !u_zbv. reflexivity. Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma wchk_ok : forall wr, 1 <= wr <= 1000000 ->
  (zx 18446744073708551615 <? zx (sw32 (sw32 wr + 18446744073708551615))) = true.
Proof. intros wr H. unfold zx, sw32. apply Z.ltb_lt. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]. lia. Qed.
Lemma wchk_bad : forall wr, 0 <= wr < 2 ^ 32 -> ~ (1 <= wr <= 1000000) ->
  (zx 18446744073708551615 <? zx (sw32 (sw32 wr + 18446744073708551615))) = false.
Proof. intros wr H H'. unfold zx, sw32. apply Z.ltb_ge. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma bv_signed_Z_small : forall a, 0 <= a < 2 ^ 63 -> bv_signed (Z_to_bv 64 a) = a.
Proof.
  intros a Ha. unfold bv_signed. rewrite u_zbv, zx_small by lia. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia.
Qed.

Lemma v_mulh_small : forall a b, 0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 -> a * b < 2 ^ 63 ->
  v_mulh (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 0.
Proof.
  intros a b Ha Hb Hab. unfold v_mulh. rewrite !bv_signed_Z_small by lia. rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.div_small by nia. reflexivity.
Qed.
