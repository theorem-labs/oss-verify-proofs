(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Malloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma size_classes_length : length size_classes = 48%nat.
Proof. reflexivity. Qed.

Lemma size_classes_bounds : Forall (fun x => 1 <= x <= 8191) size_classes.
Proof.
  apply Forall_forall. intros x Hx. unfold size_classes in Hx.
  repeat (destruct Hx as [<-|Hx]; [lia|]). destruct Hx.
Qed.

Lemma size_class_bound sc : 0 <= sc < 48 -> 1 <= size_class sc <= 8191.
Proof.
  intros H. unfold size_class.
  apply (Forall_forall (fun x => 1 <= x <= 8191) size_classes); [apply size_classes_bounds|].
  apply nth_In. rewrite size_classes_length. lia.
Qed.

(* [comment removed for export] *)
Lemma mask_upto_nonneg k : 0 <= k -> 0 <= mask_upto k.
Proof. intros. unfold mask_upto. assert (0 < 2 ^ (k + 1)) by (apply Z.pow_pos_nonneg; lia). lia. Qed.

Lemma testbit_mask_upto k i : 0 <= k -> 0 <= i -> Z.testbit (mask_upto k) i = (i <=? k).
Proof.
  intros Hk Hi. unfold mask_upto. replace (2 ^ (k + 1) - 1) with (Z.pred (2 ^ (k + 1))) by lia.
  rewrite <- Z.ones_equiv. destruct (Z.leb_spec i k).
  - apply Z.ones_spec_low. lia.
  - apply Z.ones_spec_high. lia.
Qed.

Lemma testbit_bit i j : 0 <= i -> 0 <= j -> Z.testbit (bit i) j = (i =? j).
Proof.
  intros Hi Hj. unfold bit. destruct (Z.eqb_spec i j) as [<-|NE].
  - apply Z.pow2_bits_true. exact Hi.
  - apply Z.pow2_bits_false. lia.
Qed.

Lemma bits_below_bound n a : 0 <= a -> 0 <= n -> (forall i, 0 <= i -> Z.testbit a i = true -> i < n) -> a < 2 ^ n.
Proof.
  intros Ha Hn Hb. destruct (Z.lt_ge_cases a (2 ^ n)) as [|Hge]; [assumption|]. exfalso.
  assert (Hl : n <= Z.log2 a) by (apply Z.log2_le_pow2; lia).
  assert (Ht : Z.testbit a (Z.log2 a) = true) by (apply Z.bit_log2; lia).
  specialize (Hb (Z.log2 a) ltac:(apply Z.log2_nonneg) Ht). lia.
Qed.

Lemma testbit_false_above n a i : 0 <= a < 2 ^ n -> n <= i -> Z.testbit a i = false.
Proof.
  intros Ha Hi. destruct (Z.eq_dec a 0) as [->|NZ]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|].
  apply (Z.lt_le_trans _ (2 ^ n)); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.
End RC__1.
