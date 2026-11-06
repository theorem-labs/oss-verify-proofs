(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Bool Lia Znumtheory.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VWord.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma testbit_high_small m k : 0 <= m < 2 ^ 64 -> 64 <= k -> Z.testbit m k = false.
Proof.
  intros Hm Hk. destruct (Z.eq_dec m 0) as [->|Hnz]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|].
  apply Z.lt_le_trans with 64; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma land_low64 z m : 0 <= m < 2 ^ 64 -> Z.land z m = Z.land (zwrap 64 z) m.
Proof.
  intros Hm. unfold zwrap. apply Z.bits_inj'. intros k Hk. rewrite !Z.land_spec.
  destruct (Z.lt_ge_cases k 64) as [Hlt|Hge].
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite (testbit_high_small m k) by lia. now rewrite !andb_false_r.
Qed.

Lemma zwrap_land a b : zwrap 64 (Z.land a b) = Z.land (zwrap 64 a) (zwrap 64 b).
Proof.
  unfold zwrap. apply Z.bits_inj'. intros k Hk. rewrite !Z.land_spec.
  destruct (Z.lt_ge_cases k 64).
  - rewrite !Z.mod_pow2_bits_low by lia. apply Z.land_spec.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma zwrap_lor a b : zwrap 64 (Z.lor a b) = Z.lor (zwrap 64 a) (zwrap 64 b).
Proof.
  unfold zwrap. apply Z.bits_inj'. intros k Hk. rewrite !Z.lor_spec.
  destruct (Z.lt_ge_cases k 64).
  - rewrite !Z.mod_pow2_bits_low by lia. apply Z.lor_spec.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma zwrap_lxor a b : zwrap 64 (Z.lxor a b) = Z.lxor (zwrap 64 a) (zwrap 64 b).
Proof.
  unfold zwrap. apply Z.bits_inj'. intros k Hk. rewrite !Z.lxor_spec.
  destruct (Z.lt_ge_cases k 64).
  - rewrite !Z.mod_pow2_bits_low by lia. apply Z.lxor_spec.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma pow2_log2_bound a j : 0 <= a -> 0 <= j -> a < 2 ^ j <-> (a = 0 \/ Z.log2 a < j).
Proof.
  intros Ha Hj. destruct (Z.eq_dec a 0) as [->|Hnz].
  - split; [auto|]. intros _. apply pow2_pos; lia.
  - rewrite <- Z.log2_lt_pow2 by lia. split; [auto|]. intros [H|H]; [lia|auto].
Qed.

Lemma land_upper a m : 0 <= a -> 0 <= m -> 0 <= Z.land a m <= m /\ Z.land a m <= a.
Proof.
  intros Ha Hm.
  assert (H0 : 0 <= Z.land a m) by (apply Z.land_nonneg; auto).
  pose proof (Z.sub_land_same_l a m) as E1.    (* [comment removed for export] *)
  pose proof (Z.sub_land_same_l m a) as E2.
  rewrite Z.land_comm in E2.
  assert (0 <= Z.land a (Z.lnot m)) by (apply Z.land_nonneg; auto).
  assert (0 <= Z.land m (Z.lnot a)) by (apply Z.land_nonneg; auto).
  lia.
Qed.

Lemma lor_lower a b : 0 <= a -> 0 <= b -> a <= Z.lor a b /\ b <= Z.lor a b.
Proof.
  intros Ha Hb.
  pose proof (Z.sub_lor_l_same_l b a) as E1.   (* [comment removed for export] *)
  pose proof (Z.sub_lor_l_same_l a b) as E2.   (* [comment removed for export] *)
  rewrite Z.lor_comm in E2.
  assert (0 <= Z.land b (Z.lnot a)) by (apply Z.land_nonneg; auto).
  assert (0 <= Z.land a (Z.lnot b)) by (apply Z.land_nonneg; auto).
  lia.
Qed.

Lemma lor_upper a b j : 0 <= j -> 0 <= a < 2 ^ j -> 0 <= b < 2 ^ j -> 0 <= Z.lor a b < 2 ^ j.
Proof.
  intros Hj Ha Hb.
  assert (H0 : 0 <= Z.lor a b) by (apply Z.lor_nonneg; lia).
  split; [exact H0|].
  destruct (Z.eq_dec a 0) as [->|Haz]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|Hbz]; [rewrite Z.lor_0_r; lia|].
  pose proof (lor_lower a b ltac:(lia) ltac:(lia)) as [L1 L2].
  apply Z.log2_lt_pow2; [lia|]. rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma lxor_upper a b j : 0 <= j -> 0 <= a < 2 ^ j -> 0 <= b < 2 ^ j -> 0 <= Z.lxor a b < 2 ^ j.
Proof.
  intros Hj Ha Hb.
  assert (H0 : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia).
  split; [exact H0|].
  destruct (Z.eq_dec a 0) as [->|Haz]; [rewrite Z.lxor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|Hbz]; [rewrite Z.lxor_0_r; lia|].
  destruct (Z.eq_dec (Z.lxor a b) 0) as [->|Hnz]; [apply pow2_pos; lia|].
  apply Z.log2_lt_pow2; [lia|].
  eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|].
  apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma land_upper64 a m : 0 <= a < 2 ^ 64 -> 0 <= m -> 0 <= Z.land a m < 2 ^ 64.
Proof. intros. pose proof (land_upper a m ltac:(lia) ltac:(lia)). lia. Qed.

(* [comment removed for export] *)
Lemma land_lowmask u k : 0 <= k -> Z.land u (2 ^ k - 1) = u mod 2 ^ k.
Proof. intros. rewrite land_mask_zwrap by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ones64_mod k : 0 <= k <= 64 -> (2 ^ 64 - 1) mod 2 ^ k = 2 ^ k - 1.
Proof.
  intros Hk. symmetry. apply (Z.mod_unique_pos (2 ^ 64 - 1) (2 ^ k) (2 ^ (64 - k) - 1)).
  - pose proof (pow2_pos k ltac:(lia)). lia.
  - rewrite Z.mul_sub_distr_l, <- Z.pow_add_r by lia. replace (k + (64 - k)) with 64 by lia. lia.
Qed.

Lemma alignmask_ldiff k : 0 <= k <= 64 -> 2 ^ 64 - 2 ^ k = Z.ldiff (Z.ones 64) (Z.ones k).
Proof.
  intros Hk. rewrite Z.ldiff_land, <- Z.sub_land_same_l, Z.land_ones by lia.
  unfold Z.ones. rewrite !Z.shiftl_1_l. change (Z.pred (2 ^ 64)) with (2 ^ 64 - 1).
  rewrite ones64_mod by lia. lia.
Qed.

Lemma land_alignmask u k : 0 <= u < 2 ^ 64 -> 0 <= k <= 64 ->
  Z.land u (2 ^ 64 - 2 ^ k) = u - u mod 2 ^ k.
Proof.
  intros Hu Hk.
  rewrite <- (Z.land_ones u k) by lia. rewrite Z.sub_land_same_l.
  rewrite alignmask_ldiff by lia.
  apply Z.bits_inj'. intros i Hi.
  rewrite !Z.land_spec, Z.ldiff_spec, Z.lnot_spec, !Z.testbit_ones by lia.
  destruct (Z.lt_ge_cases i 64) as [Hlt|Hge].
  - replace (0 <=? i) with true by (symmetry; apply Z.leb_le; lia).
    replace (i <? 64) with true by (symmetry; apply Z.ltb_lt; lia). simpl. reflexivity.
  - rewrite (testbit_high_small u i) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lor_disjoint a b j : 0 <= j -> 0 <= a -> a mod 2 ^ j = 0 -> 0 <= b < 2 ^ j ->
  Z.lor a b = a + b.
Proof.
  intros Hj Ha Hm Hb.
  assert (Hl : Z.land a b = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i j) as [Hlt|Hge].
    - rewrite <- (Z.mod_pow2_bits_low a j i) by lia. rewrite Hm, Z.bits_0. reflexivity.
    - destruct (Z.eq_dec b 0) as [->|Hnz]; [now rewrite Z.bits_0, andb_false_r|].
      rewrite (Z.bits_above_log2 b i); [now rewrite andb_false_r|lia|].
      apply Z.lt_le_trans with j; [|lia]. apply Z.log2_lt_pow2; lia. }
  pose proof (Z.add_lor_land a b) as E. rewrite Hl in E. lia.
Qed.

(* [comment removed for export] *)
Lemma shiftr_zwrap64 x k : 0 <= k <= 64 ->
  zwrap 64 x / 2 ^ k = zwrap (64 - k) (x / 2 ^ k).
Proof.
  intros Hk. unfold zwrap.
  pose proof (pow2_pos k ltac:(lia)) as Pk. pose proof (pow2_pos (64 - k) ltac:(lia)) as Pr.
  assert (E64 : 2 ^ 64 = 2 ^ k * 2 ^ (64 - k)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  apply Z.mod_unique_pos with (q := x / 2 ^ 64).
  - split; [apply Z.div_pos; [apply Z.mod_pos_bound|]; lia|].
    apply Z.div_lt_upper_bound; [lia|]. rewrite <- E64. apply Z.mod_pos_bound. lia.
  - (* [comment removed for export] *)
    pose proof (Z.div_mod x (2 ^ 64) ltac:(lia)) as Hx.
    rewrite Hx at 1. rewrite E64 at 1.
    replace (2 ^ k * 2 ^ (64 - k) * (x / 2 ^ 64) + x mod 2 ^ 64)
      with (x mod 2 ^ 64 + (2 ^ (64 - k) * (x / 2 ^ 64)) * 2 ^ k) by lia.
    rewrite Z.div_add by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma lxor_allones u : 0 <= u < 2 ^ 64 -> Z.lxor u (2 ^ 64 - 1) = 2 ^ 64 - 1 - u.
Proof.
  intros Hu. change (2 ^ 64 - 1) with (Z.ones 64).
  rewrite <- Z.ldiff_ones_l_low; try lia.
  - rewrite Z.ldiff_land, <- Z.sub_land_same_l, Z.land_comm, Z.land_ones by lia.
    rewrite Z.mod_small by lia. reflexivity.
  - destruct (Z.eq_dec u 0) as [->|]; [simpl; lia|]. apply Z.log2_lt_pow2; lia.
Qed.
