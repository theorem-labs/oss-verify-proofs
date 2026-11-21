(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BvAux.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Lemma pow2_pos : forall n, 0 <= n -> 0 < 2 ^ n.
Proof. intros n Hn. apply Z.pow_pos_nonneg; lia. Qed.

Lemma shiftr_lt_pow2 : forall h b n, 0 <= h < 2 ^ b -> 0 <= n <= b -> h / 2 ^ n < 2 ^ (b - n).
Proof.
  intros h b n Hh Hn. pose proof (pow2_pos n ltac:(lia)).
  apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (n + (b - n)) with b by lia. lia.
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

End WithSegs.
