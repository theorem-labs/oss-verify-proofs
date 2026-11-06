(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnWordsCorrect BnDivWords
  BnKaraCorrect BnInv BnSpecs BnSpecs2 BnDivSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma lval_firstn_small : forall l m, limbs l -> lval l < Bp m -> lval (firstn m l) = lval l.
Proof.
  intros l m Hl Hv. destruct (Nat.le_gt_cases (length l) m) as [Hle|Hgt]; [rewrite firstn_all2 by lia; reflexivity|].
  pose proof (lval_split_le m l ltac:(lia)) as E.
  pose proof (lval_nonneg _ (limbs_firstn m l Hl)). pose proof (lval_nonneg _ (limbs_skipn m l Hl)) as Hs.
  pose proof (Bp_pos m). assert (lval (skipn m l) = 0) by nia. nia.
Qed.

Lemma kara_j_facts : forall al bl : nat, (16 <= al)%nat -> (16 <= bl)%nat -> (al <= bl + 1)%nat -> (bl <= al + 1)%nat ->
  Z.of_nat al + Z.of_nat bl <= 32001 ->
  let kj := Z.to_nat (num_bits_word (Z.of_nat (Nat.max al bl)) - 1) in
  let j := Nat.pow 2 kj in
  (4 <= kj)%nat /\ (j <= Nat.max al bl)%nat /\ (Nat.max al bl < 2 * j)%nat /\ Z.of_nat j <= 8192.
Proof.
  intros al bl Ha Hb H1 H2 Hsum. cbv zeta. set (m := Nat.max al bl).
  assert (Hm16 : 16 <= Z.of_nat m) by (subst m; lia).
  assert (Hm : Z.of_nat m <= 16001) by (subst m; lia).
  destruct (num_bits_word_spec (Z.of_nat m) ltac:(lia)) as (B1 & B2 & B3).
  set (bits := num_bits_word (Z.of_nat m)) in *.
  set (kj := Z.to_nat (bits - 1)). assert (Ekj : Z.of_nat kj = bits - 1) by (subst kj; lia).
  assert (Ej : Z.of_nat (Nat.pow 2 kj) = 2 ^ (bits - 1)) by (rewrite Nat2Z.inj_pow, Ekj; reflexivity).
  assert (Hk4 : 4 <= bits - 1).
  { destruct (Z.lt_ge_cases (bits - 1) 4) as [Hlt|]; [exfalso|assumption].
    assert (2 ^ bits <= 2 ^ 4) by (apply Z.pow_le_mono_r; lia). lia. }
  assert (Hk13 : bits - 1 <= 13).
  { destruct (Z.le_gt_cases (bits - 1) 13) as [|Hgt]; [assumption|exfalso].
    assert (2 ^ 14 <= 2 ^ (bits - 1)) by (apply Z.pow_le_mono_r; lia). lia. }
  assert (E2 : 2 ^ bits = 2 * 2 ^ (bits - 1)).
  { replace bits with (Z.succ (bits - 1)) at 1 by lia. apply Z.pow_succ_r. lia. }
  split; [lia|]. split; [lia|]. split; [lia|].
  rewrite Ej. assert (2 ^ (bits - 1) <= 2 ^ 13) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Section MulSpec.
Context {ptr : Type}.
Local Notation LS := (lstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).

Definition same1234 (s s' : LS) : Prop :=
  getbn RB1 s' = getbn RB1 s /\ getbn RB2 s' = getbn RB2 s /\ getbn RB3 s' = getbn RB3 s /\ getbn RB4 s' = getbn RB4 s.

End MulSpec.
