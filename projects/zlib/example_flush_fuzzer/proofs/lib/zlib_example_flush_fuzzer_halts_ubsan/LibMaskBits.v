(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec SeqExec StepTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).


Lemma testbit_high : forall n a k, 0 <= n -> 0 <= a < 2^n -> n <= k -> Z.testbit a k = false.
Proof. intros. eapply Z_testbit_high; eauto. Qed.

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










Lemma land_pow2_testbit : forall a n, 0 <= a -> 0 <= n ->
  Z.land a (2^n) = 0 <-> Z.testbit a n = false.
Proof.
  intros a n Ha Hn. split.
  - intros H. apply (f_equal (fun z => Z.testbit z n)) in H.
    rewrite Z.land_spec, Z.bits_0, testbit_pow2, Z.eqb_refl, andb_true_r in H by lia. exact H.
  - intros H. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0, testbit_pow2 by lia.
    destruct (Z.eqb_spec n k) as [<-|Hne]; [rewrite H; reflexivity | apply andb_false_r].
Qed.











Lemma Z_to_bv_mod64 : forall z, Z_to_bv 64 z = Z_to_bv 64 (z mod 2^64).
Proof. intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_mod by lia. reflexivity. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
