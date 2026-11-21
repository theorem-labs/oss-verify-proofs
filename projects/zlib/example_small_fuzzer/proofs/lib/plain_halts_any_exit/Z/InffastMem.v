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
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.

Module ItableMem2.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import Logic.FunctionalExtensionality.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
End ItableMem2.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma lt_pow2_weaken : forall x n m, x < 2 ^ n -> 0 <= n <= m -> x < 2 ^ m.
Proof. intros x n m Hx Hnm. pose proof (Z.pow_le_mono_r 2 n m ltac:(lia) ltac:(lia)). lia. Qed.

Lemma pow2_pos : forall n, 0 <= n -> 0 < 2 ^ n.
Proof. intros n Hn. apply Z.pow_pos_nonneg; lia. Qed.

Lemma shiftr_lt_pow2 : forall h b n, 0 <= h < 2 ^ b -> 0 <= n <= b -> h / 2 ^ n < 2 ^ (b - n).
Proof.
  intros h b n Hh Hn. pose proof (pow2_pos n ltac:(lia)).
  apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (n + (b - n)) with b by lia. lia.
Qed.

Lemma pull1_lt : forall h b v, 0 <= h < 2 ^ b -> 0 <= b -> 0 <= v < 256 -> h + v * 2 ^ b < 2 ^ (b + 8).
Proof.
  intros h b v Hh Hb Hv. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
  pose proof (pow2_pos b Hb). nia.
Qed.
Lemma pull2_lt : forall h b v0 v1, 0 <= h < 2 ^ b -> 0 <= b -> 0 <= v0 < 256 -> 0 <= v1 < 256 ->
  h + v0 * 2 ^ b + v1 * 2 ^ (b + 8) < 2 ^ (b + 16).
Proof.
  intros h b v0 v1 Hh Hb Hv0 Hv1.
  pose proof (pull1_lt h b v0 Hh Hb Hv0) as H1.
  pose proof (pull1_lt (h + v0 * 2 ^ b) (b + 8) v1) as H2.
  replace (b + 8 + 8) with (b + 16) in H2 by lia.
  apply H2; [|lia|lia]. pose proof (pow2_pos b Hb). nia.
Qed.

Lemma mod64_id : forall a, 0 <= a < 2 ^ 64 -> a mod 2 ^ 64 = a.
Proof. intros a Ha. apply Z.mod_small. exact Ha. Qed.
Lemma mod32_id : forall a, 0 <= a < 2 ^ 32 -> a mod 2 ^ 32 = a.
Proof. intros a Ha. apply Z.mod_small. exact Ha. Qed.

Lemma land_ones_mod : forall h n, 0 <= n -> Z.land h (2 ^ n - 1) = h mod 2 ^ n.
Proof.
  intros h n Hn. replace (2 ^ n - 1) with (Z.ones n) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
  apply Z.land_ones. exact Hn.
Qed.
Lemma land_ones_range : forall h n, 0 <= n -> 0 <= Z.land h (2 ^ n - 1) < 2 ^ n.
Proof. intros h n Hn. rewrite land_ones_mod by lia. apply Z.mod_pos_bound. apply pow2_pos. lia. Qed.


Lemma code_op_eq : forall v, code_op v = v mod 256.
Proof. intros v. unfold code_op. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma code_bits_eq : forall v, code_bits v = (v / 256) mod 256.
Proof.
  intros v. unfold code_bits. change 255 with (Z.ones 8). rewrite Z.land_ones, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma code_val_eq : forall v, code_val v = (v / 65536) mod 65536.
Proof.
  intros v. unfold code_val. change 65535 with (Z.ones 16). rewrite Z.land_ones, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma code_op_range : forall v, 0 <= code_op v < 256.
Proof. intros v. rewrite code_op_eq. apply Z.mod_pos_bound. lia. Qed.
Lemma code_bits_range : forall v, 0 <= code_bits v < 256.
Proof. intros v. rewrite code_bits_eq. apply Z.mod_pos_bound. lia. Qed.
Lemma code_val_range : forall v, 0 <= code_val v < 65536.
Proof. intros v. rewrite code_val_eq. apply Z.mod_pos_bound. lia. Qed.

Section WithSegs.

Definition tab_u32 (f : Z -> Z) (n : nat) : bool :=
  forallb (fun j => (0 <=? f (Z.of_nat j)) && (f (Z.of_nat j) <? 4294967296)) (seq 0 n).
Lemma tab_u32_sound : forall f n i, tab_u32 f n = true -> 0 <= i < Z.of_nat n -> 0 <= f i < 2 ^ 32.
Proof.
  intros f n i H Hi. unfold tab_u32 in H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat i) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. change (2 ^ 32) with 4294967296. lia.
Qed.

End WithSegs.
