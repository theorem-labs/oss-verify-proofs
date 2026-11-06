(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition sm (y d : Z) : Z := Z.lor y (Z.shiftr y d).

Lemma sm_bits : forall y d b, 0 <= d -> 0 <= b -> Z.testbit (sm y d) b = Z.testbit y b || Z.testbit y (b + d).
Proof. intros y d b Hd Hb. unfold sm. rewrite Z.lor_spec, Z.shiftr_spec by lia. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint smj (x : Z) (j : nat) : Z :=
  match j with O => x | S j' => sm (smj x j') (2 ^ Z.of_nat j') end.

Lemma smj_bits : forall x j b, 0 <= b ->
  (Z.testbit (smj x j) b = true <-> exists i, 0 <= i < 2 ^ Z.of_nat j /\ Z.testbit x (b + i) = true).
Proof.
  intros x j. induction j as [|j IH]; intros b Hb; cbn [smj].
  - split.
    + intros H. exists 0. split; [cbn; lia| rewrite Z.add_0_r; exact H].
    + intros (i & Hi & H). cbn in Hi. replace i with 0 in H by lia. rewrite Z.add_0_r in H. exact H.
  - rewrite sm_bits by (try apply Z.pow_nonneg; lia). rewrite Bool.orb_true_iff, IH by lia.
    rewrite (IH (b + 2 ^ Z.of_nat j)) by (pose proof (Z.pow_nonneg 2 (Z.of_nat j)); lia).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    split.
    + intros [(i & Hi & H)|(i & Hi & H)].
      * exists i. split; [lia| exact H].
      * exists (2 ^ Z.of_nat j + i). split; [lia| rewrite Z.add_assoc; exact H].
    + intros (i & Hi & H). destruct (Z.lt_ge_cases i (2 ^ Z.of_nat j)) as [L|G].
      * left. exists i. split; [lia| exact H].
      * right. exists (i - 2 ^ Z.of_nat j). split; [lia|]. replace (b + 2 ^ Z.of_nat j + (i - 2 ^ Z.of_nat j)) with (b + i) by lia.
        exact H.
Qed.

Lemma smear_ones : forall x k, 0 <= k < 64 -> 2 ^ k <= x < 2 ^ (k + 1) -> smj x 6 = Z.ones (k + 1).
Proof.
  intros x k Hk Hx.
  assert (Hx0 : 0 < x) by (pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)); lia).
  assert (HL : Z.log2 x = k) by (apply Z.log2_unique; lia).
  apply Z.bits_inj'. intros b Hb.
  rewrite Z.testbit_ones_nonneg by lia.
  destruct (Z.testbit (smj x 6) b) eqn:E.
  - apply (smj_bits x 6 b Hb) in E. destruct E as (i & Hi & H).
    symmetry. apply Z.ltb_lt. destruct (Z.lt_ge_cases b (k + 1)) as [L|G]; [exact L|].
    rewrite Z.bits_above_log2 in H by lia. discriminate.
  - symmetry. apply Z.ltb_ge. destruct (Z.lt_ge_cases b (k + 1)) as [L|G]; [|exact G].
    exfalso. assert (T : Z.testbit (smj x 6) b = true).
    { apply (smj_bits x 6 b Hb). exists (k - b). split; [cbn; lia|]. replace (b + (k - b)) with k by lia.
      rewrite <- HL. apply Z.bit_log2. lia. }
    rewrite T in E. discriminate.
Qed.

(* [comment removed for export] *)
Definition sm64 (y d : Z) : Z := (Z.lor y (Z.shiftr y d)) mod 18446744073709551616.
Fixpoint smj64 (x : Z) (j : nat) : Z :=
  match j with O => x | S j' => sm64 (smj64 x j') (2 ^ Z.of_nat j') end.

Lemma sm64_bits : forall y d b, 0 <= d -> 0 <= b ->
  Z.testbit (sm64 y d) b = (b <? 64) && (Z.testbit y b || Z.testbit y (b + d)).
Proof.
  intros y d b Hd Hb. unfold sm64. change 18446744073709551616 with (2 ^ 64).
  destruct (Z.lt_ge_cases b 64) as [L|G].
  - rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lor_spec, Z.shiftr_spec by lia.
    rewrite (proj2 (Z.ltb_lt b 64) L). reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia. rewrite (proj2 (Z.ltb_ge b 64) G). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma smj64_smj : forall x j, 0 <= x < 2 ^ 64 -> smj64 x j = smj x j.
Proof.
  intros x j Hx. apply Z.bits_inj'. intros b Hb. revert b Hb. induction j as [|j IH]; intros b Hb; cbn [smj64 smj]; [reflexivity|].
  rewrite sm64_bits, sm_bits by (try apply Z.pow_nonneg; lia). rewrite !IH by (try (pose proof (Z.pow_nonneg 2 (Z.of_nat j))); lia).
  destruct (Z.lt_ge_cases b 64) as [L|G]; [rewrite (proj2 (Z.ltb_lt b 64) L); reflexivity|].
  rewrite (proj2 (Z.ltb_ge b 64) G). cbn [andb]. symmetry.
  apply Bool.orb_false_iff. split.
  - destruct (Z.testbit (smj x j) b) eqn:E; [|reflexivity]. apply smj_bits in E; [|lia]. destruct E as (i & Hi & H).
    rewrite Z.bits_above_log2 in H; [discriminate| lia|].
    destruct (Z.eq_dec x 0) as [E0|E0]; [subst x; cbn; lia|]. pose proof (Z.log2_lt_pow2 x 64 ltac:(lia)). lia.
  - destruct (Z.testbit (smj x j) (b + 2 ^ Z.of_nat j)) eqn:E; [|reflexivity].
    apply smj_bits in E; [|pose proof (Z.pow_nonneg 2 (Z.of_nat j)); lia]. destruct E as (i & Hi & H).
    rewrite Z.bits_above_log2 in H; [discriminate| pose proof (Z.pow_nonneg 2 (Z.of_nat j)); lia|].
    destruct (Z.eq_dec x 0) as [E0|E0]; [subst x; cbn; pose proof (Z.pow_nonneg 2 (Z.of_nat j)); lia|].
    pose proof (Z.log2_lt_pow2 x 64 ltac:(lia)). pose proof (Z.pow_nonneg 2 (Z.of_nat j)). lia.
Qed.

(* [comment removed for export] *)
Definition pc_chain (y : Z) : Z :=
  let p1 := (y - Z.land (Z.shiftr y 1) 6148914691236517205) mod 18446744073709551616 in
  let p2 := Z.land p1 3689348814741910323 + Z.land (Z.shiftr p1 2) 3689348814741910323 in
  let p3 := (p2 + Z.shiftr (p2 mod 18446744073709551616) 4) mod 18446744073709551616 in
  let p4 := Z.land p3 1085102592571150095 in
  let p5 := (p4 * 72340172838076673) mod 18446744073709551616 in
  Z.shiftr p5 56.

Lemma pc_chain_all : forallb (fun k => Z.eqb (pc_chain ((Z.lxor (Z.ones (Z.of_nat k + 1)) 18446744073709551615)
                                                          mod 18446744073709551616)) (63 - Z.of_nat k))
                       (seq 0 64) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pc_chain_clz : forall k, 0 <= k < 64 ->
  pc_chain ((Z.lxor (Z.ones (k + 1)) 18446744073709551615) mod 18446744073709551616) = 63 - k.
Proof.
  intros k Hk. pose proof pc_chain_all as H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat k)). rewrite Z2Nat.id in H by lia. apply Z.eqb_eq. apply H.
  apply in_seq. lia.
Qed.

(* [comment removed for export] *)
Lemma msb_exists : forall x, 0 < x < 2 ^ 64 -> exists k, 0 <= k < 64 /\ 2 ^ k <= x < 2 ^ (k + 1).
Proof.
  intros x Hx. exists (Z.log2 x). pose proof (Z.log2_spec x ltac:(lia)) as [H1 H2].
  split; [split; [apply Z.log2_nonneg| apply Z.log2_lt_pow2; lia]|].
  replace (Z.log2 x + 1) with (Z.succ (Z.log2 x)) by lia. lia.
Qed.
