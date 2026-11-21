(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ModelRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableModel2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition lstep (lft c : Z) : Z := 2 * lft - c.

Lemma left_rec_S' : forall count n len lft, len <= MAXBITS ->
  left_rec count (S n) len lft =
  if lstep lft (arr_get count len) <? 0 then None
  else left_rec count n (len + 1) (lstep lft (arr_get count len)).
Proof.
  intros count n len lft Hlen. rewrite left_rec_S. unfold lstep.
  replace (len <=? MAXBITS) with true by (symmetry; apply Z.leb_le; lia).
  rewrite Z.shiftl_mul_pow2, Z.pow_1_r, Z.mul_comm by lia. reflexivity.
Qed.


Fixpoint psum (cnt : arr) (n : nat) : Z :=
  match n with
  | O => 0
  | S n' => psum cnt n' + arr_get cnt (Z.of_nat n)
  end.

Lemma psum_S : forall cnt n, psum cnt (S n) = psum cnt n + arr_get cnt (Z.of_nat (S n)).
Proof. reflexivity. Qed.

Lemma itm_offs_k_psum : forall cnt k j, 1 <= k <= 15 -> 1 <= j <= k ->
  arr_get (itm_offs_k cnt k) j = wrap16 (psum cnt (Z.to_nat (j - 1))).
Proof.
  intros cnt k. 
  assert (GEN : forall n, (n <= 14)%nat -> forall j, 1 <= j <= 1 + Z.of_nat n ->
            arr_get (itm_offs_k cnt (1 + Z.of_nat n)) j = wrap16 (psum cnt (Z.to_nat (j - 1)))).
  { induction n as [|n IH]; intros Hn j Hj.
    - cbn [Z.of_nat Z.add]. rewrite itm_offs_k_1.
      assert (j = 1) by lia. subst j. rewrite arr_get_set_same by (rewrite arr_len_make; lia).
      cbn. rewrite wrap16_mod. reflexivity.
    - replace (1 + Z.of_nat (S n)) with (1 + Z.of_nat n + 1) by lia.
      rewrite itm_offs_k_step by lia. cbv zeta.
      destruct (Z.eq_dec j (1 + Z.of_nat n + 1)) as [->|Hne].
      + rewrite arr_get_set_same by (rewrite itm_offs_k_len; lia).
        rewrite IH by lia.
        replace (Z.to_nat (1 + Z.of_nat n + 1 - 1)) with (S (Z.to_nat (1 + Z.of_nat n - 1))) by lia.
        rewrite psum_S. replace (Z.of_nat (S (Z.to_nat (1 + Z.of_nat n - 1)))) with (1 + Z.of_nat n) by lia.
        rewrite !wrap16_mod. rewrite Zplus_mod_idemp_l. reflexivity.
      + rewrite arr_get_set_other by lia. apply IH; lia. }
  intros Hk Hj. replace k with (1 + Z.of_nat (Z.to_nat (k - 1))) by lia.
  apply GEN; lia.
Qed.

Lemma itm_offs_psum : forall cnt j, 1 <= j <= 15 ->
  arr_get (itm_offs cnt) j = wrap16 (psum cnt (Z.to_nat (j - 1))).
Proof. intros cnt j Hj. rewrite itm_offs_eq. unfold MAXBITS. apply itm_offs_k_psum; lia. Qed.

