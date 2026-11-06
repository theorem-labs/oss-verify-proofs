(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition smear_step (a s : Z) : Z := Z.lor a (Z.shiftr a s).
Definition smear6 (x : Z) : Z :=
  let x1 := smear_step x 1 in let x2 := smear_step x1 2 in let x3 := smear_step x2 4 in
  let x4 := smear_step x3 8 in let x5 := smear_step x4 16 in smear_step x5 32.

(* [comment removed for export] *)
Definition topset (a lo : Z) : Prop :=
  0 <= a < 2 ^ 47 /\ forall n, Z.max 0 lo <= n <= 46 -> Z.testbit a n = true.

Lemma lor_lt_pow2 : forall a b k, 0 <= a < 2 ^ k -> 0 <= b < 2 ^ k -> 0 <= Z.lor a b < 2 ^ k.
Proof.
  intros a b k Ha Hb. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec a 0) as [->|Ha0]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|Hb0]; [rewrite Z.lor_0_r; lia|].
  assert (Hk : 0 < k).
  { destruct (Z.lt_ge_cases 0 k) as [|Hk]; [assumption|]. exfalso.
    assert (2 ^ k <= 2 ^ 0) by (destruct (Z.eq_dec k 0) as [->|]; [lia| rewrite (Z.pow_neg_r 2 k) by lia; cbn; lia]).
    rewrite Z.pow_0_r in *. lia. }
  apply Z.log2_lt_pow2. { pose proof (Z.lor_nonneg a b). assert (Z.lor a b <> 0). { intros E. apply Z.lor_eq_0_iff in E. lia. } lia. }
  rewrite Z.log2_lor by lia. apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma shiftr_lt_pow2 : forall a s k, 0 <= a < 2 ^ k -> 0 <= s -> 0 <= Z.shiftr a s < 2 ^ k.
Proof.
  intros a s k Ha Hs. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; [lia|apply Z.pow_pos_nonneg; lia]|].
  apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
  assert (1 <= 2 ^ s) by (pose proof (Z.pow_le_mono_r 2 0 s ltac:(lia) Hs) as X; rewrite Z.pow_0_r in X; lia). nia.
Qed.

Lemma topset_step : forall a lo s, 0 <= s -> s <= 47 - lo -> topset a lo -> topset (smear_step a s) (lo - s).
Proof.
  intros a lo s Hs Hsl [Ha Hb]. unfold smear_step. split.
  - apply lor_lt_pow2; [lia|]. apply shiftr_lt_pow2; lia.
  - intros n Hn. rewrite Z.lor_spec. apply orb_true_iff.
    destruct (Z.le_gt_cases (Z.max 0 lo) n) as [H|H].
    + left. apply Hb. lia.
    + right. rewrite Z.shiftr_spec by lia. apply Hb. lia.
Qed.

Lemma topset_start : forall x, 2 ^ 46 <= x < 2 ^ 47 -> topset x 46.
Proof.
  intros x Hx. split; [lia|]. intros n Hn. assert (n = 46) by lia. subst n.
  apply Z.testbit_true; [lia|]. replace (x / 2 ^ 46) with 1; [reflexivity|].
  apply Z.div_unique with (r := x - 2 ^ 46); [left; lia | lia].
Qed.

Lemma topset_full : forall a lo, lo <= 0 -> topset a lo -> a = 2 ^ 47 - 1.
Proof.
  intros a lo Hlo [Ha Hb]. apply Z.bits_inj'. intros n Hn.
  destruct (Z.le_gt_cases 47 n) as [H|H].
  - assert (L1 : forall c, 0 <= c < 2 ^ 47 -> Z.testbit c n = false).
    { intros c Hc. destruct (Z.eq_dec c 0) as [->|Hc0]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. pose proof (proj1 (Z.log2_lt_pow2 c 47 ltac:(lia)) ltac:(lia)). lia. }
    rewrite (L1 a) by lia. rewrite (L1 (2 ^ 47 - 1)) by lia. reflexivity.
  - rewrite Hb by lia. symmetry. replace (2 ^ 47 - 1) with (Z.ones 47) by (rewrite Z.ones_equiv; reflexivity). apply Z.ones_spec_low. lia.
Qed.

Theorem smear6_47 : forall x, 2 ^ 46 <= x < 2 ^ 47 -> smear6 x = 2 ^ 47 - 1.
Proof.
  intros x Hx. unfold smear6. cbv zeta.
  apply (topset_full _ (46 - 1 - 2 - 4 - 8 - 16 - 32)); [lia|].
  repeat (apply topset_step; [lia|lia|]). apply topset_start. exact Hx.
Qed.
