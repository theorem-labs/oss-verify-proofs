(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool Btauto.
(* [comment removed for export] *)
#[global] Unset Lia Cache.
#[global] Unset Nia Cache.
#[global] Unset Nra Cache.
Open Scope Z_scope.

Definition smear_step (s : Z) (x : Z) : Z := Z.lor x (Z.shiftr x s).
(* [comment removed for export] *)
Definition smear6 (x : Z) : Z :=
  smear_step 32 (smear_step 16 (smear_step 8 (smear_step 4 (smear_step 2 (smear_step 1 x))))).

Lemma smear_step_nonneg s x : 0 <= s -> 0 <= x -> 0 <= smear_step s x.
Proof. intros Hs Hx. unfold smear_step. apply Z.lor_nonneg. split; [exact Hx| apply Z.shiftr_nonneg; exact Hx]. Qed.

Lemma smear_step_spec s x n : 0 <= s -> 0 <= n ->
  Z.testbit (smear_step s x) n = Z.testbit x n || Z.testbit x (n + s).
Proof. intros Hs Hn. unfold smear_step. rewrite Z.lor_spec, Z.shiftr_spec by lia. reflexivity. Qed.

(* [comment removed for export] *)
Definition ones_from (lo : Z) (v : Z) : Prop :=
  0 <= v /\ (forall n, 47 <= n -> Z.testbit v n = false) /\ (forall n, 0 <= n -> lo <= n <= 46 -> Z.testbit v n = true).

(* [comment removed for export] *)
Lemma ones_step s lo v : 0 <= s -> lo + s <= 47 -> ones_from lo v -> ones_from (lo - s) (smear_step s v).
Proof.
  intros Hs Hlen (Hv & Hhi & Hlo). split; [apply smear_step_nonneg; assumption|]. split.
  - intros n Hn. rewrite smear_step_spec by lia. rewrite Hhi by lia. rewrite Hhi by lia. reflexivity.
  - intros n Hn0 Hn. rewrite smear_step_spec by lia.
    destruct (Z_le_gt_dec lo n) as [H|H].
    + rewrite (Hlo n) by lia. reflexivity.
    + rewrite (Hlo (n + s)) by lia. apply orb_true_r.
Qed.

Lemma ones_start x : 2 ^ 46 <= x < 2 ^ 47 -> ones_from 46 x.
Proof.
  intros Hx. split; [lia|]. split.
  - intros n Hn. destruct (Z.testbit x n) eqn:E; [|reflexivity]. exfalso.
    apply Z.testbit_true in E; [|lia].
    assert (2 ^ 47 <= 2 ^ n) by (apply Z.pow_le_mono_r; lia).
    assert (x / 2 ^ n = 0) by (apply Z.div_small; lia). rewrite H0 in E. cbn in E. lia.
  - intros n Hn0 Hn. assert (n = 46) by lia. subst n.
    apply Z.testbit_true; [lia|].
    assert (x / 2 ^ 46 = 1) as ->; [| reflexivity].
    symmetry. apply Z.div_unique with (r := x - 2 ^ 46); lia.
Qed.

Lemma ones_all v : ones_from 0 v -> v = 2 ^ 47 - 1.
Proof.
  intros (Hv & Hhi & Hlo).
  replace (2 ^ 47 - 1) with (Z.ones 47) by (rewrite Z.ones_equiv; reflexivity).
  apply Z.bits_inj'. intros n Hn.
  destruct (Z_lt_le_dec n 47) as [H|H].
  - rewrite Hlo by lia. rewrite Z.ones_spec_low by lia. reflexivity.
  - rewrite Hhi by lia. rewrite Z.ones_spec_high by lia. reflexivity.
Qed.

Theorem smear6_eq x : 2 ^ 46 <= x < 2 ^ 47 -> smear6 x = 2 ^ 47 - 1.
Proof.
  intros Hx. apply ones_all. unfold smear6.
  replace 0 with (46 - 1 - 2 - 4 - 8 - 16 - 32 + 17) by lia.
  (* [comment removed for export] *)
  assert (M : forall lo lo' v, lo <= lo' -> lo <= 0 \/ lo <= lo' -> ones_from lo v -> ones_from lo' v).
  { intros lo lo' v H _ (A & B & C). split; [exact A|]. split; [exact B|]. intros n Hn0 Hn. apply C; lia. }
  apply (M (46 - 1 - 2 - 4 - 8 - 16 - 32)); [lia| lia|].
  apply ones_step; [lia| lia|]. apply ones_step; [lia| lia|]. apply ones_step; [lia| lia|].
  apply ones_step; [lia| lia|]. apply ones_step; [lia| lia|]. apply ones_step; [lia| lia|].
  apply ones_start. exact Hx.
Qed.

(* [comment removed for export] *)
Definition two64 : Z := 2 ^ 64.
Definition w64 (z : Z) : Z := z mod two64.
Definition maxva_tail (y : Z) : Z :=
  let a0 := w64 (Z.lnot y) in                       (* [comment removed for export] *)
  let a5 := Z.shiftr a0 1 in                        (* [comment removed for export] *)
  let a1 := Z.land a5 0x5555555555555555 in         (* [comment removed for export] *)
  let a0 := w64 (a0 - a1) in                        (* [comment removed for export] *)
  let a1 := Z.land a0 0x3333333333333333 in         (* [comment removed for export] *)
  let a0 := Z.shiftr a0 2 in                        (* [comment removed for export] *)
  let a0 := Z.land a0 0x3333333333333333 in         (* [comment removed for export] *)
  let a0 := w64 (a1 + a0) in                        (* [comment removed for export] *)
  let a1 := Z.shiftr a0 4 in                        (* [comment removed for export] *)
  let a0 := w64 (a0 + a1) in                        (* [comment removed for export] *)
  let a0 := Z.land a0 0x0f0f0f0f0f0f0f0f in         (* [comment removed for export] *)
  let a0 := w64 (a0 * 0x0101010101010101) in        (* [comment removed for export] *)
  let a0 := Z.shiftr a0 56 in                       (* [comment removed for export] *)
  let a0 := w64 (- (a0 mod 2 ^ 32)) in              (* [comment removed for export] *)
  let a1 := w64 (-1) in                             (* [comment removed for export] *)
  let a0 := w64 (Z.shiftl a1 (a0 mod 64)) in        (* [comment removed for export] *)
  w64 (Z.lnot a0).                                  (* [comment removed for export] *)

Lemma maxva_tail_const : maxva_tail (2 ^ 47 - 1) = 2 ^ 47 - 1.
Proof. vm_compute. reflexivity. Qed.

Theorem maxva_eq x : 2 ^ 46 <= x < 2 ^ 47 -> maxva_tail (smear6 x) = 2 ^ 47 - 1.
Proof. intros Hx. rewrite (smear6_eq x Hx). exact maxva_tail_const. Qed.
