(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec SeqExec StepTac.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma testbit_pow2 : forall n k, 0 <= n -> 0 <= k -> Z.testbit (2^n) k = (n =? k).
Proof.
  intros n k Hn Hk. rewrite <- (Z.shiftl_1_l n), Z.shiftl_spec by lia.
  destruct (Z.eqb_spec n k) as [->|Hne].
  - rewrite Z.sub_diag. reflexivity.
  - destruct (Z.lt_ge_cases (k - n) 0) as [Hl|Hg].
    + apply Z.testbit_neg_r. lia.
    + rewrite Z.bits_above_log2; [reflexivity | lia |]. apply Z.log2_lt_pow2; [lia|].
      apply Z.lt_le_trans with (2^1)%Z; [simpl; lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma land_ones_mod : forall x k, 0 <= x -> 0 <= k -> Z.land x (2^k - 1) = x mod 2^k.
Proof. intros x k Hx Hk. rewrite <- (Z.land_ones x k) by lia. unfold Z.ones. rewrite Z.shiftl_1_l. f_equal; lia. Qed.

Lemma swrap32_cases : forall a, 0 <= a < 2^32 ->
  (a < 2^31 /\ bv_swrap 32 a = a) \/ (2^31 <= a /\ bv_swrap 32 a = a - 2^32).
Proof.
  intros a Ha. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  destruct (Z.lt_ge_cases a (2^31)) as [Hl|Hg].
  - left. split; [lia|]. rewrite Z.mod_small by lia. lia.
  - right. split; [lia|]. rewrite <- (Z.mod_unique (a + 2^31) (2^32) 1 (a + 2^31 - 2^32)); lia.
Qed.

Lemma u_lw_lo : forall a, 0 <= a < 2^31 -> bv_unsigned (v_lw (Z_to_bv 64 a)) = a.
Proof.
  intros a Ha. unfold v_lw. rewrite (u_Z2bv a) by lia.
  destruct (swrap32_cases a ltac:(lia)) as [[_ E]|[? _]]; [|lia]. rewrite E. apply u_Z2bv; lia.
Qed.

Lemma land_pow2_testbit : forall a n, 0 <= a -> 0 <= n ->
  Z.land a (2^n) = 0 <-> Z.testbit a n = false.
Proof.
  intros a n Ha Hn. split.
  - intros H. apply (f_equal (fun z => Z.testbit z n)) in H.
    rewrite Z.land_spec, Z.bits_0, testbit_pow2, Z.eqb_refl, andb_true_r in H by lia. exact H.
  - intros H. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0, testbit_pow2 by lia.
    destruct (Z.eqb_spec n k) as [<-|Hne]; [rewrite H; reflexivity | apply andb_false_r].
Qed.

Lemma v_andi_Z : forall x m, 0 <= x < 2^64 -> 0 <= m < 2^64 ->
  v_andi (Z_to_bv 64 x) m = Z_to_bv 64 (Z.land x m).
Proof. intros x m Hx Hm. unfold v_andi. rewrite u_Z2bv by lia. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma v_and_Z : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  v_and (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.land x y).
Proof. intros. unfold v_and. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma v_slli_Z : forall x k, 0 <= x -> 0 <= k -> x * 2^k < 2^64 ->
  v_slli (Z_to_bv 64 x) k = Z_to_bv 64 (x * 2^k).
Proof.
  intros x k Hx Hk Hb. unfold v_slli. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
  rewrite u_Z2bv by nia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma v_srli_Z : forall x k, 0 <= x < 2^64 -> 0 <= k ->
  v_srli (Z_to_bv 64 x) k = Z_to_bv 64 (x / 2^k).
Proof. intros x k Hx Hk. unfold v_srli. rewrite u_Z2bv by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma v_mul_Z : forall x y, 0 <= x -> 0 <= y -> x < 2^64 -> y < 2^64 ->
  v_mul (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x * y).
Proof. intros. unfold v_mul. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma v_add_ZZ : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  v_add (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof. intros. unfold v_add. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma v_sub_ZZ : forall x y, 0 <= y <= x -> x < 2^64 ->
  v_sub (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x - y).
Proof. intros. unfold v_sub. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma c_ltu_Z : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  c_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros. unfold c_ltu, bv_ltu. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma Z_to_bv_mod64 : forall z, Z_to_bv 64 z = Z_to_bv 64 (z mod 2^64).
Proof. intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_mod by lia. reflexivity. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
