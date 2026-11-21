(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.

Module BvAux.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.


Lemma mod_pow2_mod_pow2 : forall x n m, 0 <= m <= n ->
  (x mod 2^n) mod 2^m = x mod 2^m.
Proof.
  intros x n m H. apply Z.bits_inj'. intros k Hk.
  destruct (Z.lt_ge_cases k m) as [Hlt|Hge].
  - rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma Zmod_pow2_lxor : forall a b n, 0 <= n ->
  (Z.lxor a b) mod 2^n = (Z.lxor (a mod 2^n) (b mod 2^n)) mod 2^n.
Proof.
  intros a b n Hn. apply Z.bits_inj'. intros m Hm.
  destruct (Z.lt_ge_cases m n) as [Hlt|Hge].
  - rewrite !Z.mod_pow2_bits_low by lia.
    rewrite !Z.lxor_spec.
    rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma Zmod_pow2_shiftr : forall z k n m, 0 <= k -> 0 <= n -> k + n <= m ->
  (Z.shiftr (z mod 2^m) k) mod 2^n = (Z.shiftr z k) mod 2^n.
Proof.
  intros z k n m Hk Hn Hkn. apply Z.bits_inj'. intros j Hj.
  destruct (Z.lt_ge_cases j n) as [Hlt|Hge].
  - rewrite !Z.mod_pow2_bits_low by lia.
    rewrite !Z.shiftr_spec by lia.
    rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma Zland_255 : forall z, Z.land z 255 = z mod 256.
Proof.
  intro z. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma Zland_15 : forall z, Z.land z 15 = z mod 16.
Proof.
  intro z. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma Zland_1 : forall z, Z.land z 1 = z mod 2.
Proof.
  intro z. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma Zshiftr_lt_pow2 : forall a k n, 0 <= k -> 0 <= n -> 0 <= a < 2^n ->
  0 <= Z.shiftr a k < 2^n.
Proof.
  intros a k n Hk Hn Ha.
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
  split; [apply Z.div_pos; lia|].
  apply Z.le_lt_trans with a; [|lia].
  apply Z.div_le_upper_bound; nia.
Qed.

Lemma Zmod_lt_pow2 : forall a n, 0 <= n -> 0 <= a mod 2^n < 2^n.
Proof. intros a n Hn. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. Qed.

Lemma shiftr_mod_pow2 : forall z k m, 0 <= k -> k <= m ->
  Z.shiftr (z mod 2^m) k = (Z.shiftr z k) mod 2^(m-k).
Proof.
  intros z k m Hk Hkm. apply Z.bits_inj'. intros j Hj.
  rewrite Z.shiftr_spec by lia.
  destruct (Z.lt_ge_cases (j+k) m) as [Hlt|Hge].
  - rewrite Z.mod_pow2_bits_low by lia.
    rewrite Z.mod_pow2_bits_low by lia.
    rewrite Z.shiftr_spec by lia. reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia.
    rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
End BvAux.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.


Definition argv_layout_slack : Z := 4300000%Z.


Local Lemma argv_struct_arith : forall a e : Z,
  (0 <= a)%Z -> (a <= 1024)%Z -> (0 <= e)%Z -> (e <= 256)%Z ->
  (8 + (a + 1) * 8 + (e + 1) * 8 + 144 <= 10408)%Z.
Proof. intros. lia. Qed.

Local Lemma argv_sum_arith : forall a b : Z,
  (a <= 10408)%Z -> (b <= 2097152)%Z -> (a + b <= 2107560)%Z.
Proof. intros. lia. Qed.

Local Lemma argv_mod_arith : forall s m : Z,
  (0 <= s)%Z -> (0 <= m)%Z -> (m <= 2107560)%Z -> (s + 4300000 < 2^64)%Z ->
  (0 <= s + m < 2^64)%Z.
Proof. intros. lia. Qed.

Local Lemma argv_final_arith : forall s m l : Z,
  (0 <= m)%Z -> (0 <= l)%Z -> (m <= 2107560)%Z -> (l <= 131071)%Z ->
  (s + 4300000 < 2^64)%Z ->
  (s <= s + m)%Z /\ (s + m + l + 1 < 2^64)%Z.
Proof. intros. lia. Qed.

Lemma Zmod_pow2_div8 : forall z m, (8 <= m)%Z ->
  ((z mod 2^m) / 2^8)%Z = ((z / 2^8) mod 2^(m-8))%Z.
Proof.
  intros z m Hm.
  rewrite <- !Z.shiftr_div_pow2 by lia.
  apply Z.bits_inj'; intros i Hi.
  rewrite !Z.shiftr_spec by lia.
  destruct (Z.lt_ge_cases i (m - 8)) as [Hlt|Hge].
  - rewrite !Z.mod_pow2_bits_low by lia.
    rewrite Z.shiftr_spec by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
