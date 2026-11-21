(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.

Module ItMath.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma pow2_pos : forall n, 0 <= n -> 0 < 2 ^ n.
Proof. intros. apply Z.pow_pos_nonneg; lia. Qed.
Lemma pow2_split : forall a b, 0 <= b <= a -> 2 ^ a = 2 ^ (a - b) * 2 ^ b.
Proof. intros a b H. rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.

Section SigFacts.
  Variable wl : list Z.
  Hypothesis HW : forall l, 0 <= W wl l.
  Hypothesis Hlen : length wl = 16%nat.
  #[local] Set Default Proof Using "HW Hlen".

  Local Notation W := (W wl).
  Local Notation OFF := (OFF wl).
  Local Notation NZ := (NZ wl).
  Local Notation MAXL := (MAXL wl).
  Local Notation MINL := (MINL wl).
  Local Notation TM := (TM wl).
  Local Notation LEFT := (LEFT wl).
  Local Notation len_at := (len_at wl).
  Local Notation rank_at := (rank_at wl).
  Local Notation Apos := (Apos wl).
  Local Notation code := (code wl).
  Local Notation hf := (hf wl).

  Lemma W_above15 : forall l, 15 < l -> W l = 0.
  Proof. intros l Hl. unfold ItDefs.W. apply nth_overflow. rewrite Hlen. lia. Qed.


  Lemma NZ_eq : NZ = OFF 16.
  Proof. exact (@eq_refl Z (OFF 16)). Qed.

  Lemma OFF_1 : OFF 1 = 0.
  Proof. unfold ItDefs.OFF. apply sumz_nil. lia. Qed.
  Lemma OFF_step : forall l, 1 <= l -> OFF (l + 1) = OFF l + W l.
  Proof. intros l Hl. unfold ItDefs.OFF. apply sumz_snoc. lia. Qed.
  Lemma OFF_mono : forall l l', 1 <= l <= l' -> OFF l <= OFF l'.
  Proof. intros l l' H. unfold ItDefs.OFF. apply sumz_mono_hi; [intros; apply HW | lia]. Qed.
  Lemma OFF_nonneg : forall l, 0 <= OFF l.
  Proof. intros l. unfold ItDefs.OFF. apply sumz_nonneg. intros; apply HW. Qed.
  Lemma OFF_diff : forall l l', 1 <= l <= l' -> OFF l' = OFF l + sumz (fun i => W i) l l'.
  Proof.
    intros l l' H. unfold ItDefs.OFF. exact (sumz_split _ 1 l l' ltac:(lia)).
  Qed.
  Lemma NZ_nonneg : 0 <= NZ.
  Proof. unfold ItDefs.NZ. apply OFF_nonneg. Qed.

  Lemma OFF_flat : forall l l', 1 <= l <= l' -> OFF l' = OFF l ->
    forall i, l <= i < l' -> W i = 0.
  Proof.
    intros l l' H E i Hi.
    pose proof (OFF_mono l i ltac:(lia)). pose proof (OFF_mono (i + 1) l' ltac:(lia)).
    rewrite OFF_step in H1 by lia. pose proof (HW i). lia.
  Qed.

  Lemma len_at_spec : forall k, 0 <= k < NZ ->
    1 <= len_at k <= 15 /\ OFF (len_at k) <= k < OFF (len_at k + 1).
  Proof.
    intros k Hk. unfold ItDefs.len_at.
    set (p := fun l => k <? OFF (l + 1)).
    assert (Pf : forall x, p x = false -> OFF (x + 1) <= k) by (intros x; unfold p; rewrite Z.ltb_ge; tauto).
    assert (Pt : forall x, p x = true -> k < OFF (x + 1)) by (intros x; unfold p; rewrite Z.ltb_lt; tauto).
    clearbody p.
    pose proof (zsearch_bound p 1 15) as B. change (1 + Z.of_nat 15) with 16 in B.
    destruct (zsearch_cases p 1 15) as [E|[Hlt Hp]].
    - exfalso. change (1 + Z.of_nat 15) with 16 in E.
      assert (H : p 15 = false) by (apply (zsearch_before p 1 15); lia).
      apply Pf in H. rewrite NZ_eq in Hk. change (15 + 1) with 16 in H. lia.
    - change (1 + Z.of_nat 15) with 16 in Hlt.
      split; [lia|]. split.
      + destruct (Z.eq_dec (zsearch p 1 15) 1) as [E1|E1].
        * rewrite E1, OFF_1. lia.
        * assert (Hb : p (zsearch p 1 15 - 1) = false) by (apply (zsearch_before p 1 15); lia).
          apply Pf in Hb. replace (zsearch p 1 15 - 1 + 1) with (zsearch p 1 15) in Hb by lia. exact Hb.
      + apply Pt in Hp. exact Hp.
  Qed.

  Lemma len_at_unique : forall k l, 1 <= l <= 15 -> OFF l <= k < OFF (l + 1) -> len_at k = l.
  Proof.
    intros k l Hl Hk. unfold ItDefs.len_at. apply zsearch_eq.
    - cbn. lia.
    - apply Z.ltb_lt. lia.
    - intros i Hi. apply Z.ltb_ge. pose proof (OFF_mono (i + 1) l ltac:(lia)). lia.
  Qed.

  Lemma rank_at_spec : forall k, 0 <= k < NZ -> 0 <= rank_at k < W (len_at k).
  Proof.
    intros k Hk. pose proof (len_at_spec k Hk) as [Hl Ho]. unfold ItDefs.rank_at.
    rewrite OFF_step in Ho by lia. lia.
  Qed.

  Lemma len_at_mono : forall k k', 0 <= k <= k' -> k' < NZ -> len_at k <= len_at k'.
  Proof.
    intros k k' Hk Hk'.
    pose proof (len_at_spec k ltac:(lia)) as [A1 A2]. pose proof (len_at_spec k' ltac:(lia)) as [B1 B2].
    destruct (Z.le_gt_cases (len_at k) (len_at k')) as [H|H]; [exact H|].
    pose proof (OFF_mono (len_at k' + 1) (len_at k) ltac:(lia)). lia.
  Qed.

  Lemma MAXL_spec :
    0 <= MAXL <= 15 /\ (forall l, MAXL < l -> W l = 0) /\ (1 <= MAXL -> 1 <= W MAXL).
  Proof.
    unfold ItDefs.MAXL. set (q := fun i => negb (W (15 - i) =? 0)).
    assert (Qf : forall x, q x = false -> W (15 - x) = 0).
    { intros x; unfold q. destruct (Z.eqb_spec (W (15 - x)) 0); [intros _; assumption | intros X; discriminate X]. }
    assert (Qt : forall x, q x = true -> W (15 - x) <> 0).
    { intros x; unfold q. destruct (Z.eqb_spec (W (15 - x)) 0); [intros X; discriminate X | intros _; assumption]. }
    clearbody q.
    pose proof (zsearch_bound q 0 15) as B. change (0 + Z.of_nat 15) with 15 in B.
    split; [lia|]. split.
    - intros l Hl. destruct (Z.le_gt_cases l 15) as [H15|H15]; [|apply W_above15; lia].
      assert (Hq : q (15 - l) = false) by (apply (zsearch_before q 0 15); lia).
      apply Qf in Hq. replace (15 - (15 - l)) with l in Hq by lia. exact Hq.
    - intros H1. assert (Hq : q (zsearch q 0 15) = true) by (apply zsearch_found; change (0 + Z.of_nat 15) with 15; lia).
      apply Qt in Hq. pose proof (HW (15 - zsearch q 0 15)). lia.
  Qed.

  Lemma MINL_spec : 1 <= MAXL ->
    1 <= MINL <= MAXL /\ 1 <= W MINL /\ (forall l, 1 <= l < MINL -> W l = 0).
  Proof.
    intros HM. pose proof MAXL_spec as [M1 [M2 M3]]. unfold ItDefs.MINL.
    set (q := fun l => negb (W l =? 0)).
    assert (Qf : forall x, q x = false -> W x = 0).
    { intros x; unfold q. destruct (Z.eqb_spec (W x) 0); [intros _; assumption | intros X; discriminate X]. }
    assert (Qt : forall x, q x = true -> W x <> 0).
    { intros x; unfold q. destruct (Z.eqb_spec (W x) 0); [intros X; discriminate X | intros _; assumption]. }
    clearbody q.
    set (n := Z.to_nat (MAXL - 1)) in *.
    assert (Hn : Z.of_nat n = MAXL - 1) by lia.
    pose proof (zsearch_bound q 1 n) as B. rewrite Hn in B.
    assert (Hbefore : forall l, 1 <= l < zsearch q 1 n -> W l = 0).
    { intros l Hl. apply Qf. apply (zsearch_before q 1 n). exact Hl. }
    destruct (zsearch_cases q 1 n) as [E|[Hlt Hq]].
    - rewrite Hn in E. replace (1 + (MAXL - 1)) with MAXL in E by lia. rewrite E in *.
      split; [lia|]. split; [apply M3; lia|]. exact Hbefore.
    - rewrite Hn in Hlt. split; [lia|]. split; [|exact Hbefore].
      apply Qt in Hq. pose proof (HW (zsearch q 1 n)). lia.
  Qed.

  Lemma OFF_above_MAXL : forall l, MAXL + 1 <= l -> 1 <= MAXL -> OFF l = NZ.
  Proof.
    intros l Hl HM. pose proof MAXL_spec as [M1 [M2 M3]]. unfold ItDefs.NZ.
    destruct (Z.le_gt_cases l 16).
    - rewrite (OFF_diff l 16) by lia. rewrite (sumz_zero (fun i => W i)); [lia|]. intros i Hi. apply M2. lia.
    - rewrite (OFF_diff 16 l) by lia. rewrite (sumz_zero (fun i => W i)); [lia|]. intros i Hi. apply M2. lia.
  Qed.

  Lemma OFF_MAXL : 1 <= MAXL -> OFF MAXL = NZ - W MAXL.
  Proof.
    intros HM. pose proof (OFF_above_MAXL (MAXL + 1) ltac:(lia) HM). rewrite OFF_step in H by lia. lia.
  Qed.

  Lemma NZ_pos : 1 <= MAXL -> 1 <= NZ.
  Proof.
    intros HM. pose proof MAXL_spec as [M1 [M2 M3]]. pose proof (OFF_MAXL HM). pose proof (OFF_nonneg MAXL). lia.
  Qed.

  Lemma NZ_zero : MAXL = 0 -> NZ = 0.
  Proof.
    intros HM. pose proof MAXL_spec as [M1 [M2 M3]]. unfold ItDefs.NZ, ItDefs.OFF.
    apply sumz_zero. intros i Hi. apply M2. lia.
  Qed.

  Lemma MAXL_pos_of_NZ : forall k, 0 <= k < NZ -> 1 <= MAXL.
  Proof.
    intros k Hk. pose proof MAXL_spec as [M1 _].
    destruct (Z.eq_dec MAXL 0) as [E|E]; [pose proof (NZ_zero E); lia|lia].
  Qed.

  Lemma OFF_below_MINL : forall l, 1 <= l <= MINL -> 1 <= MAXL -> OFF l = 0.
  Proof.
    intros l Hl HM. pose proof (MINL_spec HM) as [A [B C]]. unfold ItDefs.OFF.
    apply sumz_zero. intros i Hi. apply C. lia.
  Qed.

  Lemma len_at_0 : 1 <= MAXL -> len_at 0 = MINL.
  Proof.
    intros HM. pose proof MAXL_spec as [M1 _]. pose proof (MINL_spec HM) as [A [B C]]. apply len_at_unique; [lia|].
    rewrite OFF_step by lia. rewrite OFF_below_MINL by lia. lia.
  Qed.

  Lemma len_at_last : 1 <= MAXL -> len_at (NZ - 1) = MAXL.
  Proof.
    intros HM. pose proof MAXL_spec as [M1 [M2 M3]]. apply len_at_unique; [lia|].
    rewrite (OFF_above_MAXL (MAXL + 1)) by lia. rewrite OFF_MAXL by lia. specialize (M3 HM). lia.
  Qed.

  Lemma len_at_range : forall k, 0 <= k < NZ -> MINL <= len_at k <= MAXL.
  Proof.
    intros k Hk. pose proof MAXL_spec as [M1 [M2 M3]].
    pose proof (MAXL_pos_of_NZ k Hk) as HM.
    rewrite <- (len_at_0 HM), <- (len_at_last HM). split; apply len_at_mono; lia.
  Qed.

  Lemma W_len_at : forall k, 0 <= k < NZ -> 1 <= W (len_at k).
  Proof. intros k Hk. pose proof (rank_at_spec k Hk). lia. Qed.

  Lemma len_at_step : forall k, 0 <= k -> k + 1 < NZ ->
    (rank_at k + 1 < W (len_at k) /\ len_at (k + 1) = len_at k /\ rank_at (k + 1) = rank_at k + 1) \/
    (rank_at k + 1 = W (len_at k) /\ len_at k < len_at (k + 1) /\ rank_at (k + 1) = 0 /\
     forall l, len_at k < l < len_at (k + 1) -> W l = 0).
  Proof.
    intros k Hk Hk1.
    pose proof (len_at_spec k ltac:(lia)) as [A1 A2]. pose proof (rank_at_spec k ltac:(lia)) as R.
    pose proof (len_at_spec (k + 1) ltac:(lia)) as [B1 B2].
    pose proof (OFF_step (len_at k) ltac:(lia)) as OS.
    destruct (Z.lt_ge_cases (rank_at k + 1) (W (len_at k))) as [H|H].
    - left. assert (E : len_at (k + 1) = len_at k).
      { apply len_at_unique; [lia|]. unfold ItDefs.rank_at in H. lia. }
      split; [exact H|]. split; [exact E|]. unfold ItDefs.rank_at. rewrite E. lia.
    - right. unfold ItDefs.rank_at in H, R |- *.
      assert (Hk1e : k + 1 = OFF (len_at k + 1)) by lia.
      assert (Hlt : len_at k < len_at (k + 1)).
      { destruct (Z.lt_ge_cases (len_at k) (len_at (k + 1))) as [X|X]; [exact X|].
        pose proof (OFF_mono (len_at (k + 1) + 1) (len_at k + 1) ltac:(lia)). lia. }
      pose proof (OFF_mono (len_at k + 1) (len_at (k + 1)) ltac:(lia)) as Hm.
      assert (E : OFF (len_at (k + 1)) = OFF (len_at k + 1)) by lia.
      split; [lia|]. split; [exact Hlt|]. split; [lia|].
      intros l Hl. apply (OFF_flat (len_at k + 1) (len_at (k + 1))); [lia| exact E | lia].
  Qed.

  Lemma last_iff : forall k, 0 <= k < NZ ->
    (k = NZ - 1 <-> (rank_at k + 1 = W (len_at k) /\ len_at k = MAXL)).
  Proof.
    intros k Hk. pose proof MAXL_spec as [M1 [M2 M3]].
    pose proof (MAXL_pos_of_NZ k Hk) as HM.
    pose proof (OFF_MAXL HM) as OM. split.
    - intros ->. rewrite (len_at_last HM). split; [|reflexivity]. unfold ItDefs.rank_at. rewrite (len_at_last HM). lia.
    - intros [R L]. unfold ItDefs.rank_at in R. rewrite L in R. lia.
  Qed.

  Lemma TM_0 : TM 0 = 0.
  Proof. unfold ItDefs.TM. apply sumz_nil. lia. Qed.
  Lemma TM_step : forall l, 0 <= l -> TM (l + 1) = TM l + W (l + 1) * 2 ^ (MAXL - (l + 1)).
  Proof. intros l Hl. unfold ItDefs.TM. rewrite sumz_snoc by lia. reflexivity. Qed.
  Lemma TM_step' : forall l, 1 <= l -> TM l = TM (l - 1) + W l * 2 ^ (MAXL - l).
  Proof. intros l Hl. pose proof (TM_step (l - 1) ltac:(lia)). replace (l - 1 + 1) with l in H by lia. exact H. Qed.
  Lemma TM_nonneg : forall l, 0 <= TM l.
  Proof. intros l. unfold ItDefs.TM. apply sumz_nonneg. intros i Hi. pose proof (HW i). pose proof (Z.pow_nonneg 2 (MAXL - i)). nia. Qed.
  Lemma TM_mono : forall l l', 0 <= l <= l' -> TM l <= TM l'.
  Proof.
    intros l l' H. unfold ItDefs.TM. apply sumz_mono_hi; [|lia].
    intros i Hi. pose proof (HW i). pose proof (Z.pow_nonneg 2 (MAXL - i)). nia.
  Qed.
  Lemma TM_diff : forall l l', 0 <= l <= l' ->
    TM l' = TM l + sumz (fun i => W i * 2 ^ (MAXL - i)) (l + 1) (l' + 1).
  Proof. intros l l' H. unfold ItDefs.TM. apply sumz_split. lia. Qed.
  Lemma TM_flat : forall l l', 0 <= l <= l' -> (forall i, l < i <= l' -> W i = 0) -> TM l' = TM l.
  Proof.
    intros l l' H Hz. rewrite (TM_diff l l') by lia. rewrite sumz_zero; [lia|]. intros i Hi. rewrite Hz by lia. lia.
  Qed.
  Lemma TM_above : forall l, MAXL <= l -> TM l = TM MAXL.
  Proof.
    intros l Hl. pose proof MAXL_spec as [M1 [M2 M3]]. apply TM_flat; [lia|]. intros i Hi. apply M2. lia.
  Qed.
  Lemma TM_mod : forall l m, 0 <= l <= m -> m <= MAXL -> TM l mod 2 ^ (MAXL - m) = 0.
  Proof.
    intros l m H Hm. remember (Z.to_nat l) as n eqn:Hn. revert l H Hn.
    induction n as [|n IH]; intros l H Hn.
    - replace l with 0 by lia. rewrite TM_0. apply Z.mod_0_l. apply Z.pow_nonzero; lia.
    - rewrite (TM_step' l) by lia.
      rewrite Z.add_mod by (apply Z.pow_nonzero; lia). rewrite (IH (l - 1)) by lia.
      rewrite (pow2_split (MAXL - l) (MAXL - m)) by lia.
      rewrite Z.mul_assoc, Z.mod_mul by (apply Z.pow_nonzero; lia). apply Z.mod_0_l. apply Z.pow_nonzero; lia.
  Qed.

  Lemma LEFT_TM : LEFT = 2 ^ (15 - MAXL) * (2 ^ MAXL - TM MAXL).
  Proof.
    pose proof MAXL_spec as [M1 [M2 M3]]. unfold ItDefs.LEFT, ItDefs.TM.
    rewrite (sumz_split _ 1 (MAXL + 1) 16) by lia.
    rewrite (sumz_zero _ (MAXL + 1) 16) by (intros i Hi; rewrite M2 by lia; lia).
    rewrite (sumz_ext (fun l => W l * 2 ^ (15 - l)) (fun l => (W l * 2 ^ (MAXL - l)) * 2 ^ (15 - MAXL)) 1 (MAXL + 1)).
    2:{ intros i Hi. rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia. f_equal. f_equal. lia. }
    rewrite sumz_scale. rewrite Z.mul_sub_distr_l, <- Z.pow_add_r by lia.
    replace (15 - MAXL + MAXL) with 15 by lia. lia.
  Qed.

  Lemma LEFT_sign :
    (LEFT < 0 <-> 2 ^ MAXL < TM MAXL) /\ (LEFT = 0 <-> TM MAXL = 2 ^ MAXL) /\ (0 < LEFT <-> TM MAXL < 2 ^ MAXL).
  Proof.
    pose proof MAXL_spec as [M1 _]. rewrite LEFT_TM.
    pose proof (pow2_pos (15 - MAXL) ltac:(lia)). nia.
  Qed.

  Lemma Apos_0 : 1 <= MAXL -> Apos 0 = 0.
  Proof.
    intros HM. pose proof (MINL_spec HM) as [A [B C]]. unfold ItDefs.Apos.
    rewrite (len_at_0 HM). unfold ItDefs.rank_at. rewrite (len_at_0 HM), (OFF_below_MINL MINL) by lia.
    rewrite (TM_flat 0 (MINL - 1)), TM_0; [lia|lia|]. intros i Hi. apply C. lia.
  Qed.

  Lemma Apos_bounds : forall k, 0 <= k < NZ ->
    TM (len_at k - 1) <= Apos k /\ Apos k + 2 ^ (MAXL - len_at k) <= TM (len_at k).
  Proof.
    intros k Hk. pose proof (rank_at_spec k Hk) as R. pose proof (len_at_spec k Hk) as [L _].
    unfold ItDefs.Apos. rewrite (TM_step' (len_at k)) by lia.
    pose proof (Z.pow_nonneg 2 (MAXL - len_at k)). nia.
  Qed.

  Lemma Apos_nonneg : forall k, 0 <= k < NZ -> 0 <= Apos k.
  Proof. intros k Hk. pose proof (Apos_bounds k Hk). pose proof (TM_nonneg (len_at k - 1)). lia. Qed.

  Lemma Apos_le_TM : forall k, 0 <= k < NZ -> Apos k + 2 ^ (MAXL - len_at k) <= TM MAXL.
  Proof.
    intros k Hk. pose proof (Apos_bounds k Hk). pose proof (len_at_range k Hk). pose proof (len_at_spec k Hk) as [L _].
    pose proof (TM_mono (len_at k) MAXL ltac:(lia)). lia.
  Qed.

  Lemma Apos_step : forall k, 0 <= k -> k + 1 < NZ -> Apos (k + 1) = Apos k + 2 ^ (MAXL - len_at k).
  Proof.
    intros k Hk Hk1. unfold ItDefs.Apos.
    destruct (len_at_step k Hk Hk1) as [[A [B C]]|[A [B [C D]]]].
    - rewrite B, C. lia.
    - rewrite C. pose proof (len_at_spec k ltac:(lia)) as [L1 _]. pose proof (len_at_spec (k+1) ltac:(lia)) as [L2 _].
      rewrite (TM_flat (len_at k) (len_at (k + 1) - 1)); [|lia|intros; apply D; lia].
      rewrite (TM_step' (len_at k)) by lia. rewrite <- A. lia.
  Qed.

  Lemma Apos_last : 1 <= MAXL -> Apos (NZ - 1) + 2 ^ (MAXL - len_at (NZ - 1)) = TM MAXL.
  Proof.
    intros HM. pose proof (NZ_pos HM). rewrite (len_at_last HM). unfold ItDefs.Apos, ItDefs.rank_at. rewrite (len_at_last HM).
    rewrite (OFF_MAXL HM). rewrite (TM_step' MAXL) by lia. replace (MAXL - MAXL) with 0 by lia. change (2 ^ 0) with 1. lia.
  Qed.

  Definition Anext (k : Z) : Z := Apos k + 2 ^ (MAXL - len_at k).

  Lemma Anext_eq : forall k, 0 <= k < NZ ->
    Anext k = (if k + 1 <? NZ then Apos (k + 1) else TM MAXL).
  Proof.
    intros k Hk. unfold Anext. destruct (Z.ltb_spec (k + 1) NZ).
    - symmetry. apply Apos_step; lia.
    - pose proof (MAXL_pos_of_NZ k Hk) as HM.
      replace k with (NZ - 1) by lia. apply Apos_last. exact HM.
  Qed.

  Lemma Apos_mono : forall k k', 0 <= k <= k' -> k' < NZ -> Apos k <= Apos k'.
  Proof.
    intros k k' H Hk'. remember (Z.to_nat (k' - k)) as n eqn:Hn. revert k' H Hk' Hn.
    induction n as [|n IH]; intros k' H Hk' Hn.
    - replace k' with k by lia. lia.
    - pose proof (IH (k' - 1) ltac:(lia) ltac:(lia) ltac:(lia)).
      pose proof (Apos_step (k' - 1) ltac:(lia) ltac:(lia)). replace (k' - 1 + 1) with k' in H1 by lia.
      pose proof (Z.pow_nonneg 2 (MAXL - len_at (k' - 1))). lia.
  Qed.

  Lemma Apos_lt : forall k k', 0 <= k < k' -> k' < NZ -> Anext k <= Apos k'.
  Proof.
    intros k k' H Hk'. unfold Anext. rewrite <- Apos_step by lia. apply Apos_mono; lia.
  Qed.

  Lemma Apos_mod : forall k, 0 <= k < NZ -> Apos k mod 2 ^ (MAXL - len_at k) = 0.
  Proof.
    intros k Hk. pose proof (len_at_spec k Hk) as [L _]. pose proof (len_at_range k Hk). unfold ItDefs.Apos.
    rewrite Z.add_mod by (apply Z.pow_nonzero; lia). rewrite Z.mod_mul by (apply Z.pow_nonzero; lia).
    rewrite (TM_mod (len_at k - 1) (len_at k)) by lia. apply Z.mod_0_l. apply Z.pow_nonzero; lia.
  Qed.

  Lemma code_mul : forall k, 0 <= k < NZ -> code k * 2 ^ (MAXL - len_at k) = Apos k.
  Proof.
    intros k Hk. unfold ItDefs.code. pose proof (Apos_mod k Hk).
    pose proof (Z.div_mod (Apos k) (2 ^ (MAXL - len_at k)) ltac:(apply Z.pow_nonzero; pose proof (len_at_range k Hk); lia)). lia.
  Qed.

  Lemma code_nonneg : forall k, 0 <= k < NZ -> 0 <= code k.
  Proof. intros k Hk. unfold ItDefs.code. apply Z.div_pos; [apply Apos_nonneg; exact Hk| apply pow2_pos; pose proof (len_at_range k Hk); lia]. Qed.

  Lemma code_bound : TM MAXL <= 2 ^ MAXL -> forall k, 0 <= k < NZ -> code k + 1 <= 2 ^ len_at k.
  Proof.
    intros HK k Hk. pose proof (Apos_le_TM k Hk). pose proof (code_mul k Hk). pose proof (len_at_range k Hk).
    pose proof (len_at_spec k Hk) as [L _].
    rewrite (pow2_split MAXL (MAXL - len_at k)) in HK by lia. replace (MAXL - (MAXL - len_at k)) with (len_at k) in HK by lia.
    pose proof (pow2_pos (MAXL - len_at k) ltac:(lia)). nia.
  Qed.

  Lemma code_succ_lt : TM MAXL <= 2 ^ MAXL -> forall k, 0 <= k -> k + 1 < NZ -> code k + 1 < 2 ^ len_at k.
  Proof.
    intros HK k Hk Hk1. pose proof (Apos_step k Hk Hk1). pose proof (code_mul k ltac:(lia)).
    pose proof (Apos_le_TM (k + 1) ltac:(lia)). pose proof (len_at_range k ltac:(lia)). pose proof (len_at_range (k+1) ltac:(lia)).
    pose proof (len_at_spec k ltac:(lia)) as [L _].
    pose proof (pow2_pos (MAXL - len_at (k + 1)) ltac:(lia)).
    rewrite (pow2_split MAXL (MAXL - len_at k)) in HK by lia. replace (MAXL - (MAXL - len_at k)) with (len_at k) in HK by lia.
    pose proof (pow2_pos (MAXL - len_at k) ltac:(lia)). nia.
  Qed.

  Lemma code_0 : 1 <= MAXL -> code 0 = 0.
  Proof. intros HM. unfold ItDefs.code. rewrite (Apos_0 HM). apply Zdiv_0_l. Qed.

  Lemma code_step : forall k, 0 <= k -> k + 1 < NZ ->
    code (k + 1) = (code k + 1) * 2 ^ (len_at (k + 1) - len_at k).
  Proof.
    intros k Hk Hk1. pose proof (len_at_mono k (k + 1) ltac:(lia) Hk1) as M.
    pose proof (len_at_range (k + 1) ltac:(lia)). pose proof (len_at_range k ltac:(lia)).
    pose proof (code_mul k ltac:(lia)) as C1. pose proof (code_mul (k + 1) ltac:(lia)) as C2.
    pose proof (Apos_step k Hk Hk1) as S.
    apply (Z.mul_reg_r _ _ (2 ^ (MAXL - len_at (k + 1)))); [apply Z.pow_nonzero; lia|].
    rewrite C2, S, <- C1. rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia.
    replace (len_at (k + 1) - len_at k + (MAXL - len_at (k + 1))) with (MAXL - len_at k) by lia. lia.
  Qed.

  Lemma hf_spec : TM MAXL <= 2 ^ MAXL -> forall k, 0 <= k < NZ -> hf k = rev (len_at k) (code k).
  Proof.
    intros HK k Hk. unfold ItDefs.hf.
    pose proof (MAXL_pos_of_NZ k Hk) as HM.
    destruct (Z.eqb_spec k 0) as [->|Hk0].
    - rewrite (code_0 HM), rev_0. reflexivity.
    - pose proof (code_succ_lt HK (k - 1) ltac:(lia) ltac:(lia)) as Hs.
      replace (k - 1 + 1) with k in Hs by lia.
      destruct (Z.ltb_spec (code (k - 1) + 1) (2 ^ len_at (k - 1))); [|lia].
      pose proof (code_step (k - 1) ltac:(lia) ltac:(lia)) as CS. replace (k - 1 + 1) with k in CS by lia.
      rewrite CS. pose proof (len_at_mono (k - 1) k ltac:(lia) ltac:(lia)).
      pose proof (len_at_spec (k - 1) ltac:(lia)) as [L _]. pose proof (code_nonneg (k - 1) ltac:(lia)).
      replace (len_at k) with (len_at (k - 1) + (len_at k - len_at (k - 1))) at 1 by lia.
      symmetry. apply rev_shift; lia.
  Qed.

  Lemma hf_N : 1 <= NZ -> hf NZ = (if code (NZ - 1) + 1 <? 2 ^ len_at (NZ - 1) then rev (len_at (NZ - 1)) (code (NZ - 1) + 1) else 0).
  Proof.
    intros H. unfold ItDefs.hf. destruct (Z.eqb_spec NZ 0) as [E|E]; [lia|reflexivity].
  Qed.

  Section Root.
    Variable root : Z.
    Hypothesis Hroot : MINL <= root <= MAXL.
    Hypothesis HM1 : 1 <= MAXL.
    #[local] Set Default Proof Using "HW Hlen Hroot HM1".

    Local Notation GR := (GR wl root).
    Local Notation Pfx := (Pfx wl root).
    Local Notation islong := (islong wl root).
    Local Notation newtable := (newtable wl root).
    Local Notation cstar := (cstar wl root).

    Lemma root_pos : 1 <= root.
    Proof. pose proof (MINL_spec HM1). lia. Qed.
    Lemma root_range : 1 <= root <= 15.
    Proof. pose proof (MINL_spec HM1). pose proof MAXL_spec. lia. Qed.
    Lemma GR_pos : 0 < GR.
    Proof. unfold ItDefs.GR. apply pow2_pos. lia. Qed.
    Lemma GR_MAXL : 2 ^ root * GR = 2 ^ MAXL.
    Proof. unfold ItDefs.GR. rewrite <- Z.pow_add_r by (pose proof root_pos; lia). f_equal. lia. Qed.

    Lemma islong_iff : forall k, 0 <= k < NZ -> (islong k = true <-> OFF (root + 1) <= k).
    Proof.
      intros k Hk. pose proof root_pos as RP. unfold ItDefs.islong. rewrite Z.ltb_lt. pose proof (len_at_spec k Hk) as [L O]. split.
      - intros H. pose proof (OFF_mono (root + 1) (len_at k) ltac:(lia)). lia.
      - intros H. destruct (Z.lt_ge_cases root (len_at k)) as [X|X]; [exact X|].
        pose proof (OFF_mono (len_at k + 1) (root + 1) ltac:(lia)). lia.
    Qed.

    Lemma Pfx_code : forall k, 0 <= k < NZ -> islong k = true ->
      Pfx k = code k / 2 ^ (len_at k - root).
    Proof.
      intros k Hk HL. unfold ItDefs.islong in HL. apply Z.ltb_lt in HL.
      unfold ItDefs.Pfx, ItDefs.GR. rewrite <- (code_mul k Hk). pose proof (len_at_range k Hk).
      rewrite (pow2_split (MAXL - root) (MAXL - len_at k)) by lia.
      replace (MAXL - root - (MAXL - len_at k)) with (len_at k - root) by lia.
      rewrite Z.div_mul_cancel_r; [reflexivity | apply Z.pow_nonzero; lia | apply Z.pow_nonzero; lia].
    Qed.

    Lemma Pfx_nonneg : forall k, 0 <= k < NZ -> 0 <= Pfx k.
    Proof. intros k Hk. unfold ItDefs.Pfx. apply Z.div_pos; [apply Apos_nonneg; exact Hk | apply GR_pos]. Qed.

    Lemma Pfx_bound : TM MAXL <= 2 ^ MAXL -> forall k, 0 <= k < NZ -> Pfx k < 2 ^ root.
    Proof.
      intros HK k Hk. unfold ItDefs.Pfx. apply Z.div_lt_upper_bound; [apply GR_pos|].
      rewrite (Z.mul_comm GR), GR_MAXL. pose proof (Apos_le_TM k Hk). pose proof (pow2_pos (MAXL - len_at k) ltac:(pose proof (len_at_range k Hk); lia)). lia.
    Qed.

    Lemma Apos_decomp : forall k, 0 <= k < NZ -> islong k = true ->
      Apos k = Pfx k * GR + (code k mod 2 ^ (len_at k - root)) * 2 ^ (MAXL - len_at k) /\
      0 <= code k mod 2 ^ (len_at k - root) < 2 ^ (len_at k - root) /\
      2 ^ (len_at k - root) * 2 ^ (MAXL - len_at k) = GR.
    Proof.
      intros k Hk HL. rewrite (Pfx_code k Hk HL). unfold ItDefs.islong in HL. apply Z.ltb_lt in HL.
      pose proof (len_at_range k Hk). rewrite <- (code_mul k Hk).
      assert (E : 2 ^ (len_at k - root) * 2 ^ (MAXL - len_at k) = GR).
      { unfold ItDefs.GR. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
      split; [|split; [apply Z.mod_pos_bound; apply pow2_pos; lia| exact E]].
      rewrite <- E. pose proof (Z.div_mod (code k) (2 ^ (len_at k - root)) ltac:(apply Z.pow_nonzero; lia)). nia.
    Qed.

    Lemma no_straddle : forall k, 0 <= k < NZ -> islong k = true -> Anext k <= (Pfx k + 1) * GR.
    Proof.
      intros k Hk HL. unfold Anext. pose proof (Apos_decomp k Hk HL) as [D [B E]].
      pose proof (pow2_pos (MAXL - len_at k) ltac:(pose proof (len_at_range k Hk); lia)). nia.
    Qed.

    Lemma Pfx_lower : forall k, 0 <= k < NZ -> Pfx k * GR <= Apos k < (Pfx k + 1) * GR.
    Proof.
      intros k Hk. unfold ItDefs.Pfx. pose proof GR_pos.
      pose proof (Z.div_mod (Apos k) GR ltac:(lia)). pose proof (Z.mod_pos_bound (Apos k) GR ltac:(lia)). nia.
    Qed.

    Lemma islong_mono : forall k k', 0 <= k <= k' -> k' < NZ -> islong k = true -> islong k' = true.
    Proof.
      intros k k' H Hk' HL. unfold ItDefs.islong in *. apply Z.ltb_lt in HL. apply Z.ltb_lt.
      pose proof (len_at_mono k k' H Hk'). lia.
    Qed.

    Lemma Pfx_mono : forall k k', 0 <= k <= k' -> k' < NZ -> Pfx k <= Pfx k'.
    Proof.
      intros k k' H Hk'. unfold ItDefs.Pfx. apply Z.div_le_mono; [apply GR_pos | apply Apos_mono; lia].
    Qed.

    Lemma Pfx_step : forall k, 0 <= k -> k + 1 < NZ -> islong k = true ->
      Pfx (k + 1) = Pfx k \/ (Pfx (k + 1) = Pfx k + 1 /\ Apos (k + 1) = (Pfx k + 1) * GR).
    Proof.
      intros k Hk Hk1 HL. pose proof (no_straddle k ltac:(lia) HL) as NS. unfold Anext in NS.
      rewrite <- (Apos_step k Hk Hk1) in NS.
      pose proof (Pfx_lower k ltac:(lia)) as [A1 A2]. pose proof (Pfx_lower (k + 1) ltac:(lia)) as [B1 B2].
      pose proof (Apos_mono k (k + 1) ltac:(lia) Hk1). pose proof GR_pos.
      destruct (Z.eq_dec (Apos (k + 1)) ((Pfx k + 1) * GR)) as [E|E].
      - right. split; [|exact E]. rewrite E in B1, B2.
        assert (Pfx k + 1 - 1 < Pfx (k + 1)) by nia. assert (Pfx (k + 1) < Pfx k + 2) by nia. lia.
      - left. assert (Apos (k + 1) < (Pfx k + 1) * GR) by lia.
        assert (Pfx (k + 1) < Pfx k + 1) by nia. assert (Pfx k - 1 < Pfx (k + 1)) by nia. lia.
    Qed.

    Definition K0 : Z := OFF (root + 1).

    Lemma K0_range : 0 <= K0 <= NZ.
    Proof.
      unfold K0. split; [apply OFF_nonneg|]. unfold ItDefs.NZ. apply OFF_mono. pose proof root_range. lia.
    Qed.

    Lemma K0_pos : 1 <= K0.
    Proof.
      unfold K0. pose proof (MINL_spec HM1) as [A [B C]]. pose proof (OFF_mono (MINL + 1) (root + 1) ltac:(lia)).
      rewrite OFF_step in H by lia. pose proof (OFF_nonneg MINL). lia.
    Qed.

    Lemma Apos_K0 : K0 < NZ -> Apos K0 = TM root.
    Proof.
      intros HK. pose proof K0_range. pose proof root_range as RR. pose proof (len_at_spec K0 ltac:(lia)) as [L O].
      pose proof (proj2 (islong_iff K0 ltac:(lia)) ltac:(unfold K0; lia)) as HL.
      unfold ItDefs.islong in HL. apply Z.ltb_lt in HL.
      pose proof (OFF_mono (root + 1) (len_at K0) ltac:(lia)) as M. fold K0 in M.
      assert (E : OFF (len_at K0) = K0) by lia.
      unfold ItDefs.Apos, ItDefs.rank_at. rewrite E, Z.sub_diag, Z.mul_0_l, Z.add_0_r.
      apply TM_flat; [lia|]. intros i Hi.
      apply (OFF_flat (root + 1) (len_at K0)); [lia| unfold K0 in E |- *; lia | lia].
    Qed.

    Lemma TM_root_GR : TM root mod GR = 0.
    Proof. unfold ItDefs.GR. apply TM_mod; pose proof root_range; lia. Qed.

    Lemma group_start : forall k, 0 <= k < NZ -> newtable k = true -> Apos k = Pfx k * GR.
    Proof.
      intros k Hk HN. unfold ItDefs.newtable in HN.
      apply Bool.andb_true_iff in HN as [HL HN]. pose proof GR_pos as G.
      destruct (Z.eq_dec k 0) as [->|Hk0].
      { exfalso. unfold ItDefs.islong in HL. apply Z.ltb_lt in HL. rewrite (len_at_0 HM1) in HL. lia. }
      destruct (islong (k - 1)) eqn:E.
      - cbn [negb orb] in HN. apply Bool.negb_true_iff in HN.
        destruct (Z.eqb_spec (Pfx k) (Pfx (k - 1))) as [|NE]; [discriminate HN|].
        destruct (Pfx_step (k - 1) ltac:(lia) ltac:(lia) E) as [E'|[E1 E2]].
        + replace (k - 1 + 1) with k in E' by lia. congruence.
        + replace (k - 1 + 1) with k in E1, E2 by lia. rewrite E2, E1. reflexivity.
      - assert (Hk0' : k = K0).
        { pose proof (proj1 (islong_iff k Hk) HL).
          destruct (Z_le_gt_dec (OFF (root + 1)) (k - 1)) as [l|l].
          + pose proof (proj2 (islong_iff (k - 1) ltac:(lia)) l) as X. rewrite X in E. discriminate E.
          + unfold K0. lia. }
        subst k. rewrite Apos_K0 by lia. unfold ItDefs.Pfx. rewrite Apos_K0 by lia.
        pose proof TM_root_GR. pose proof (Z.div_mod (TM root) GR ltac:(lia)). lia.
    Qed.

    Local Notation lay := (lay wl root).
    Local Notation noff := (noff wl root).
    Local Notation curr := (curr wl root).
    Local Notation used := (used wl root).

    Lemma cstar_spec : forall P c0, 1 <= c0 <= MAXL - root ->
      c0 <= cstar P c0 <= MAXL - root /\
      (MAXL <= root + cstar P c0 \/ (P + 1) * GR <= TM (root + cstar P c0)) /\
      (forall c, c0 <= c < cstar P c0 -> root + c < MAXL /\ TM (root + c) < (P + 1) * GR).
    Proof.
      intros P c0 Hc0. pose proof root_range as RR. pose proof MAXL_spec as [MM _]. unfold ItDefs.cstar.
      set (p := fun c => (MAXL <=? root + c) || ((P + 1) * GR <=? TM (root + c))).
      assert (Pt : forall c, p c = true -> MAXL <= root + c \/ (P + 1) * GR <= TM (root + c)).
      { intros c. unfold p. rewrite Bool.orb_true_iff, !Z.leb_le. tauto. }
      assert (Pf : forall c, p c = false -> root + c < MAXL /\ TM (root + c) < (P + 1) * GR).
      { intros c. unfold p. rewrite Bool.orb_false_iff, !Z.leb_gt. tauto. }
      assert (Pm : p (MAXL - root) = true).
      { unfold p. apply Bool.orb_true_iff. left. apply Z.leb_le. lia. }
      clearbody p.
      pose proof (zsearch_bound p c0 16) as B. change (Z.of_nat 16) with 16 in B.
      assert (Hle : zsearch p c0 16 <= MAXL - root).
      { destruct (Z.le_gt_cases (zsearch p c0 16) (MAXL - root)) as [X|X]; [exact X|]. exfalso.
        pose proof (zsearch_before p c0 16 (MAXL - root) ltac:(lia)) as Y. rewrite Pm in Y. discriminate Y. }
      split; [lia|]. split.
      - apply Pt. apply zsearch_found. change (Z.of_nat 16) with 16. lia.
      - intros c Hc. apply Pf. apply (zsearch_before p c0 16). exact Hc.
    Qed.

    Lemma lay_0 : lay 0 = (0, root, 2 ^ root).
    Proof. reflexivity. Qed.

    Lemma lay_S : forall k, 0 <= k ->
      lay (k + 1) = (if newtable (k + 1)
                     then (noff k + 2 ^ curr k, cstar (Pfx (k + 1)) (len_at (k + 1) - root),
                           used k + 2 ^ cstar (Pfx (k + 1)) (len_at (k + 1) - root))
                     else lay k).
    Proof.
      intros k Hk. unfold ItDefs.noff, ItDefs.curr, ItDefs.used, ItDefs.lay.
      replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia. cbn [lay_n].
      replace (Z.of_nat (S (Z.to_nat k))) with (k + 1) by lia.
      destruct (lay_n wl root (Z.to_nat k)) as [[no cu] us]. reflexivity.
    Qed.

    Lemma lay_S_new : forall k, 0 <= k -> newtable (k + 1) = true ->
      noff (k + 1) = noff k + 2 ^ curr k /\
      curr (k + 1) = cstar (Pfx (k + 1)) (len_at (k + 1) - root) /\
      used (k + 1) = used k + 2 ^ curr (k + 1).
    Proof.
      intros k Hk HN. pose proof (lay_S k Hk) as E. rewrite HN in E.
      assert (E2 : curr (k + 1) = cstar (Pfx (k + 1)) (len_at (k + 1) - root)).
      { unfold ItDefs.curr at 1. rewrite E. reflexivity. }
      rewrite E2. unfold ItDefs.noff at 1. unfold ItDefs.used at 1. rewrite E. cbn [fst snd].
      repeat split; reflexivity.
    Qed.

    Lemma lay_S_same : forall k, 0 <= k -> newtable (k + 1) = false -> lay (k + 1) = lay k.
    Proof. intros k Hk HN. pose proof (lay_S k Hk) as E. rewrite HN in E. exact E. Qed.

    Lemma lay_same_proj : forall k, 0 <= k -> newtable (k + 1) = false ->
      noff (k + 1) = noff k /\ curr (k + 1) = curr k /\ used (k + 1) = used k.
    Proof.
      intros k Hk HN. unfold ItDefs.noff, ItDefs.curr, ItDefs.used. rewrite (lay_S_same k Hk HN). repeat split; reflexivity.
    Qed.

    Lemma newtable_long : forall k, newtable k = true -> islong k = true.
    Proof. intros k H. unfold ItDefs.newtable in H. apply Bool.andb_true_iff in H. tauto. Qed.

    Lemma not_newtable : forall k, 0 <= k -> k + 1 < NZ -> newtable (k + 1) = false -> islong (k + 1) = true ->
      islong k = true /\ Pfx (k + 1) = Pfx k.
    Proof.
      intros k Hk Hk1 HN HL. unfold ItDefs.newtable in HN. rewrite HL in HN. cbn [andb] in HN.
      apply Bool.orb_false_iff in HN as [A B]. replace (k + 1 - 1) with k in A, B by lia.
      apply Bool.negb_false_iff in A. apply Bool.negb_false_iff in B. apply Z.eqb_eq in B. split; assumption.
    Qed.

    Lemma lay_inv : forall k, 0 <= k < NZ ->
      (islong k = false -> noff k = 0 /\ curr k = root /\ used k = 2 ^ root) /\
      (islong k = true ->
         2 ^ root <= noff k /\ 1 <= len_at k - root <= curr k /\ curr k <= MAXL - root /\
         used k = noff k + 2 ^ curr k /\
         (MAXL <= root + curr k \/ (Pfx k + 1) * GR <= TM (root + curr k))).
    Proof.
      intros k Hk. remember (Z.to_nat k) as n eqn:Hn. revert k Hk Hn.
      induction n as [|n IH]; intros k Hk Hn.
      - replace k with 0 by lia. split.
        + intros _. unfold ItDefs.noff, ItDefs.curr, ItDefs.used. rewrite lay_0. repeat split; reflexivity.
        + intros HL. exfalso. unfold ItDefs.islong in HL. apply Z.ltb_lt in HL. rewrite (len_at_0 HM1) in HL. lia.
      - specialize (IH (k - 1) ltac:(lia) ltac:(lia)). destruct IH as [IHs IHl].
        replace k with (k - 1 + 1) by lia.
        destruct (newtable (k - 1 + 1)) eqn:HN.
        + pose proof (lay_S_new (k - 1) ltac:(lia) HN) as [E1 [E2 E3]].
          pose proof (newtable_long _ HN) as HL. split; [intros X; rewrite HL in X; discriminate X|]. intros _.
          pose proof HL as HL'. unfold ItDefs.islong in HL'. apply Z.ltb_lt in HL'.
          pose proof (len_at_range (k - 1 + 1) ltac:(lia)) as LR.
          pose proof (cstar_spec (Pfx (k - 1 + 1)) (len_at (k - 1 + 1) - root) ltac:(lia)) as [C1 [C2 C3]].
          rewrite <- E2 in C1, C2.
          assert (Hprev : 2 ^ root <= noff (k - 1) + 2 ^ curr (k - 1) /\ used (k - 1) = noff (k - 1) + 2 ^ curr (k - 1)).
          { destruct (islong (k - 1)) eqn:HLp.
            - destruct (IHl eq_refl) as [X1 [X2 [X3 [X4 _]]]]. pose proof (Z.pow_nonneg 2 (curr (k - 1))). lia.
            - destruct (IHs eq_refl) as [X1 [X2 X3]]. rewrite X1, X2, X3. lia. }
          destruct Hprev as [Hno Hus].
          split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. exact C2.
        + pose proof (lay_same_proj (k - 1) ltac:(lia) HN) as [E1 [E2 E3]]. rewrite E1, E2, E3.
          split.
          * intros HS. apply IHs. destruct (islong (k - 1)) eqn:X; [|reflexivity].
            rewrite (islong_mono (k - 1) (k - 1 + 1) ltac:(lia) ltac:(lia) X) in HS. discriminate HS.
          * intros HL. destruct (not_newtable (k - 1) ltac:(lia) ltac:(lia) HN HL) as [HLp HP].
            destruct (IHl HLp) as [X1 [X2 [X3 [X4 X5]]]]. rewrite HP.
            pose proof HL as HL'. unfold ItDefs.islong in HL'. apply Z.ltb_lt in HL'.
            assert (Hfit : len_at (k - 1 + 1) - root <= curr (k - 1)).
            { destruct X5 as [X5|X5]; [pose proof (len_at_range (k - 1 + 1) ltac:(lia)); lia|].
              pose proof (Pfx_lower (k - 1 + 1) ltac:(lia)) as [_ PL]. rewrite HP in PL.
              pose proof (Apos_bounds (k - 1 + 1) ltac:(lia)) as [AB _].
              destruct (Z.le_gt_cases (len_at (k - 1 + 1) - root) (curr (k - 1))) as [Y|Y]; [exact Y|]. exfalso.
              pose proof (TM_mono (root + curr (k - 1)) (len_at (k - 1 + 1) - 1) ltac:(pose proof root_range; lia)). lia. }
            repeat split; try lia.
    Qed.

    Lemma used_eq : forall k, 0 <= k < NZ -> used k = noff k + 2 ^ curr k.
    Proof.
      intros k Hk. destruct (lay_inv k Hk) as [A B]. destruct (islong k) eqn:E.
      - destruct (B eq_refl) as [_ [_ [_ [X _]]]]. exact X.
      - destruct (A eq_refl) as [X [Y Z']]. rewrite X, Y, Z'. reflexivity.
    Qed.

    Lemma curr_range : forall k, 0 <= k < NZ -> 1 <= curr k <= 15 /\ 0 <= len_at k - ItDefs.drop wl root k <= curr k /\ 0 <= noff k.
    Proof.
      intros k Hk. pose proof root_range. destruct (lay_inv k Hk) as [A B]. unfold ItDefs.drop. destruct (islong k) eqn:E.
      - destruct (B eq_refl) as [X1 [X2 [X3 [X4 X5]]]]. pose proof MAXL_spec. pose proof (Z.pow_nonneg 2 root). lia.
      - destruct (A eq_refl) as [X [Y Z']]. rewrite X, Y. unfold ItDefs.islong in E. apply Z.ltb_ge in E.
        pose proof (len_at_spec k Hk). lia.
    Qed.

    Lemma used_mono : forall k k', 0 <= k <= k' -> k' < NZ -> used k <= used k'.
    Proof.
      intros k k' H Hk'. remember (Z.to_nat (k' - k)) as n eqn:Hn. revert k' H Hk' Hn.
      induction n as [|n IH]; intros k' H Hk' Hn.
      - replace k' with k by lia. lia.
      - specialize (IH (k' - 1) ltac:(lia) ltac:(lia) ltac:(lia)). replace k' with (k' - 1 + 1) by lia.
        destruct (newtable (k' - 1 + 1)) eqn:HN.
        + pose proof (lay_S_new (k' - 1) ltac:(lia) HN) as [_ [_ E]]. rewrite E. pose proof (Z.pow_nonneg 2 (curr (k' - 1 + 1))). lia.
        + pose proof (lay_same_proj (k' - 1) ltac:(lia) HN) as [_ [_ E]]. rewrite E. exact IH.
    Qed.

    Lemma used_lower : forall k, 0 <= k < NZ -> 2 ^ root <= used k.
    Proof.
      intros k Hk. pose proof (used_mono 0 k ltac:(lia) ltac:(lia)). unfold ItDefs.used in H at 1. rewrite lay_0 in H. cbn [snd] in H. exact H.
    Qed.

    Lemma find_code : forall t, 0 <= t < TM MAXL -> exists k, 0 <= k < NZ /\ Apos k <= t < Anext k.
    Proof.
      intros t Ht. pose proof (NZ_pos HM1) as HN.
      set (p := fun k => t <? Anext k).
      assert (Pt : forall k, p k = true -> t < Anext k) by (intros k; unfold p; rewrite Z.ltb_lt; tauto).
      assert (Pf : forall k, p k = false -> Anext k <= t) by (intros k; unfold p; rewrite Z.ltb_ge; tauto).
      clearbody p.
      set (n := Z.to_nat NZ). assert (Hn : Z.of_nat n = NZ) by lia.
      pose proof (zsearch_bound p 0 n) as B. rewrite Hn in B.
      destruct (zsearch_cases p 0 n) as [E|[Hlt Hp]].
      - exfalso. rewrite Hn in E.
        assert (X : p (NZ - 1) = false) by (apply (zsearch_before p 0 n); lia). apply Pf in X.
        rewrite (Anext_eq (NZ - 1)) in X by lia. replace (NZ - 1 + 1) with NZ in X by lia.
        destruct (Z.ltb_spec NZ NZ); lia.
      - rewrite Hn in Hlt. exists (zsearch p 0 n). split; [lia|]. split; [|apply Pt; exact Hp].
        destruct (Z.eq_dec (zsearch p 0 n) 0) as [E0|E0].
        + rewrite E0. rewrite (Apos_0 HM1). lia.
        + assert (X : p (zsearch p 0 n - 1) = false) by (apply (zsearch_before p 0 n); lia). apply Pf in X.
          rewrite (Anext_eq (zsearch p 0 n - 1)) in X by lia. replace (zsearch p 0 n - 1 + 1) with (zsearch p 0 n) in X by lia.
          destruct (Z.ltb_spec (zsearch p 0 n) NZ); lia.
    Qed.

    Lemma TM_root_P0 : TM root = (TM root / GR) * GR.
    Proof. pose proof TM_root_GR. pose proof GR_pos. pose proof (Z.div_mod (TM root) GR ltac:(lia)). lia. Qed.

    Lemma found_long : forall j, 0 <= j < NZ -> TM root < Anext j -> islong j = true.
    Proof.
      intros j Hj Ht. pose proof K0_range as KR.
      destruct (Z.lt_ge_cases j K0) as [X|X].
      - exfalso. destruct (Z.eq_dec K0 NZ) as [E|E].
        +
          pose proof (Anext_eq j Hj) as AE.
          assert (Anext j <= TM MAXL).
          { rewrite AE. destruct (Z.ltb_spec (j + 1) NZ); [|lia]. pose proof (Apos_le_TM (j + 1) ltac:(lia)). pose proof (Z.pow_nonneg 2 (MAXL - len_at (j+1))). lia. }
          assert (TM MAXL = TM root).
          { apply TM_flat; [pose proof root_range; lia|]. intros i Hi.
            unfold K0 in E. rewrite NZ_eq in E.
            apply (OFF_flat (root + 1) 16); [pose proof root_range; lia| exact (eq_sym E) | pose proof MAXL_spec; lia]. }
          lia.
        + pose proof (Apos_lt j K0 ltac:(lia) ltac:(lia)). rewrite Apos_K0 in H by lia. lia.
      - apply (proj2 (islong_iff j Hj)). unfold K0 in X. exact X.
    Qed.

    Lemma found_short : forall j, 0 <= j < NZ -> Apos j < TM root -> islong j = false.
    Proof.
      intros j Hj Ht. pose proof K0_range as KR. destruct (islong j) eqn:E; [|reflexivity]. exfalso.
      pose proof (proj1 (islong_iff j Hj) E) as X. fold K0 in X.
      pose proof (Apos_mono K0 j ltac:(lia) ltac:(lia)). rewrite Apos_K0 in H by lia. lia.
    Qed.

    Lemma group_of : forall j, 0 <= j < NZ -> islong j = true ->
      exists g, 0 <= g <= j /\ newtable g = true /\ Pfx g = Pfx j /\
        (forall i, g <= i <= j -> lay i = lay g /\ Pfx i = Pfx g /\ islong i = true).
    Proof.
      intros j Hj HL. remember (Z.to_nat j) as n eqn:Hn. revert j Hj HL Hn.
      induction n as [n IH] using (well_founded_induction Wf_nat.lt_wf); intros j Hj HL Hn.
      destruct (newtable j) eqn:HN.
      - exists j. split; [lia|]. split; [exact HN|]. split; [reflexivity|].
        intros i Hi. replace i with j by lia. split; [reflexivity|]. split; [reflexivity|]. exact HL.
      - destruct (Z.eq_dec j 0) as [->|Hj0].
        { exfalso. unfold ItDefs.islong in HL. apply Z.ltb_lt in HL. rewrite (len_at_0 HM1) in HL. lia. }
        pose proof (not_newtable (j - 1) ltac:(lia) ltac:(lia)) as NN. replace (j - 1 + 1) with j in NN by lia.
        destruct (NN HN HL) as [HLp HP].
        destruct (IH (Z.to_nat (j - 1)) ltac:(lia) (j - 1) ltac:(lia) HLp eq_refl) as [g [G1 [G2 [G3 G4]]]].
        exists g. split; [lia|]. split; [exact G2|]. split; [lia|].
        intros i Hi. destruct (Z.eq_dec i j) as [->|Hij].
        + pose proof (lay_S_same (j - 1) ltac:(lia)) as LS. replace (j - 1 + 1) with j in LS by lia.
          rewrite (LS HN). destruct (G4 (j - 1) ltac:(lia)) as [X [Y _]]. rewrite X, <- Y, HP. repeat split; try reflexivity. exact HL.
        + apply G4. lia.
    Qed.
    Hypothesis HC : TM MAXL = 2 ^ MAXL.
    #[local] Set Default Proof Using "HW Hlen Hroot HM1 HC".

    Lemma in_group : forall P t, TM root / GR <= P < 2 ^ root -> P * GR <= t < (P + 1) * GR ->
      exists j, 0 <= j < NZ /\ islong j = true /\ Pfx j = P /\ Apos j <= t < Anext j.
    Proof.
      intros P t HP Ht. pose proof GR_pos as G.
      assert (Htr : 0 <= t < TM MAXL).
      { rewrite HC, <- GR_MAXL. pose proof (TM_nonneg root). pose proof TM_root_P0.
        assert (0 <= TM root / GR) by (apply Z.div_pos; lia). split; [nia|].
        assert ((P + 1) * GR <= 2 ^ root * GR) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
      destruct (find_code t Htr) as [j [Hj Hjt]]. exists j.
      assert (HL : islong j = true).
      { apply found_long; [exact Hj|]. pose proof TM_root_P0. nia. }
      split; [exact Hj|]. split; [exact HL|]. split; [|exact Hjt].
      pose proof (Pfx_lower j Hj) as [A B]. pose proof (no_straddle j Hj HL) as NS.
      assert (Pfx j * GR < (P + 1) * GR) by lia. assert (P * GR < (Pfx j + 1) * GR) by lia.
      assert (Pfx j < P + 1) by nia. assert (P < Pfx j + 1) by nia. lia.
    Qed.

    Lemma prefix_has_group : forall P, TM root / GR <= P < 2 ^ root ->
      exists g, 0 <= g < NZ /\ newtable g = true /\ Pfx g = P.
    Proof.
      intros P HP. pose proof GR_pos as G.
      destruct (in_group P (P * GR) HP ltac:(nia)) as [j [Hj [HL [HPj _]]]].
      clear HP. subst P. remember (Z.to_nat j) as n eqn:Hn. revert j Hj HL Hn.
      induction n as [n IH] using (well_founded_induction Wf_nat.lt_wf); intros j Hj HL Hn.
      destruct (newtable j) eqn:HN.
      - exists j. split; [lia|]. split; [exact HN | reflexivity].
      - destruct (Z.eq_dec j 0) as [->|Hj0].
        { exfalso. unfold ItDefs.islong in HL. apply Z.ltb_lt in HL. rewrite (len_at_0 HM1) in HL. lia. }
        pose proof (not_newtable (j - 1) ltac:(lia) ltac:(lia)) as NN. replace (j - 1 + 1) with j in NN by lia.
        destruct (NN HN HL) as [HLp HP].
        destruct (IH (Z.to_nat (j - 1)) ltac:(lia) (j - 1) ltac:(lia) HLp eq_refl) as [g [G1 [G2 G3]]].
        exists g. split; [lia|]. split; [exact G2|]. rewrite G3. symmetry. exact HP.
    Qed.

  End Root.
End SigFacts.
End ItMath.

Module ItSort.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItMath.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma countz_nil : forall x, countz x [] = 0.
Proof. reflexivity. Qed.
Lemma countz_cons : forall x a l, countz x (a :: l) = (if x =? a then 1 else 0) + countz x l.
Proof.
  intros x a l. unfold countz. cbn [filter]. destruct (x =? a); [rewrite zlength_cons|]; lia.
Qed.
Lemma countz_app : forall x l1 l2, countz x (l1 ++ l2) = countz x l1 + countz x l2.
Proof.
  intros x l1 l2. induction l1 as [|a l1 IH]; [cbn; reflexivity|].
  cbn [app]. rewrite !countz_cons, IH. lia.
Qed.
Lemma countz_nonneg : forall x l, 0 <= countz x l.
Proof. intros. unfold countz. apply zlength_nonneg. Qed.
Lemma countz_le_length : forall x l, countz x l <= zlength l.
Proof.
  intros x l. induction l as [|a l IH]; [unfold countz; cbn [filter]; rewrite !zlength_nil; lia|]. rewrite countz_cons, zlength_cons. destruct (x =? a); lia.
Qed.

Lemma firstn_S_nth : forall {A} (l : list A) n d, (n < length l)%nat ->
  firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
  intros A l. induction l as [|a l IH]; intros n d Hn; [cbn in Hn; lia|].
  destruct n as [|n]; [reflexivity|]. cbn [firstn nth]. rewrite (IH n d) by (cbn in Hn; lia). reflexivity.
Qed.

Lemma countz_firstn_S : forall x l n, (n < length l)%nat ->
  countz x (firstn (S n) l) = countz x (firstn n l) + (if x =? nth n l 0 then 1 else 0).
Proof.
  intros x l n Hn. rewrite (firstn_S_nth l n 0 Hn). rewrite countz_app, countz_cons, countz_nil. lia.
Qed.

Lemma countz_firstn_le : forall x l n, countz x (firstn n l) <= countz x l.
Proof.
  intros x l n. rewrite <- (firstn_skipn n l) at 2. rewrite countz_app. pose proof (countz_nonneg x (skipn n l)). lia.
Qed.

Lemma countz_firstn_mono : forall x l n m, (n <= m)%nat -> countz x (firstn n l) <= countz x (firstn m l).
Proof.
  intros x l n m H. rewrite <- (firstn_skipn n (firstn m l)), firstn_firstn.
  replace (Nat.min n m) with n by lia. rewrite countz_app. pose proof (countz_nonneg x (skipn n (firstn m l))). lia.
Qed.


Definition sel (p : Z -> bool) (n : nat) : list Z := filter p (map Z.of_nat (seq 0 n)).

Lemma sel_S : forall p n, sel p (S n) = sel p n ++ (if p (Z.of_nat n) then [Z.of_nat n] else []).
Proof.
  intros p n. unfold sel. rewrite seq_S, map_app, filter_app. cbn [map filter Nat.add]. reflexivity.
Qed.

Lemma sel_spec : forall p n r, (r < length (sel p n))%nat ->
  let s := nth r (sel p n) 0 in
  p s = true /\ 0 <= s < Z.of_nat n /\ length (sel p (Z.to_nat s)) = r.
Proof.
  intros p n. induction n as [|n IH]; intros r Hr.
  - cbn in Hr. lia.
  - rewrite sel_S in *. destruct (p (Z.of_nat n)) eqn:E.
    + rewrite app_length in Hr. cbn [length] in Hr.
      destruct (Nat.lt_ge_cases r (length (sel p n))) as [H|H].
      * cbn zeta. rewrite app_nth1 by exact H. destruct (IH r H) as [A [B C]]. repeat split; try assumption; lia.
      * assert (r = length (sel p n)) by lia. subst r. cbn zeta.
        rewrite app_nth2, Nat.sub_diag by lia. cbn [nth]. rewrite Nat2Z.id.
        repeat split; try assumption; lia.
    + rewrite app_nil_r in *. destruct (IH r Hr) as [A [B C]]. cbn zeta. repeat split; try assumption; lia.
Qed.

Lemma sel_count : forall p s, p (Z.of_nat s) = true ->
  length (sel p (S s)) = S (length (sel p s)).
Proof. intros p s H. rewrite sel_S, H, app_length. cbn [length]. lia. Qed.

Lemma sel_mono : forall p n m, (n <= m)%nat -> (length (sel p n) <= length (sel p m))%nat.
Proof.
  intros p n m H. induction H as [|m H IH]; [lia|]. rewrite sel_S, app_length. lia.
Qed.


Lemma nth_map_seq : forall {B} (f : nat -> B) len n d, (n < len)%nat -> nth n (map f (seq 0 len)) d = f n.
Proof.
  intros B f len n d H. rewrite (nth_indep _ d (f 0%nat)) by (rewrite map_length, seq_length; lia).
  rewrite map_nth. rewrite seq_nth by lia. reflexivity.
Qed.

Section LL.
  Variable ll : list Z.
  Hypothesis Hll : Forall (fun l => 0 <= l <= 15) ll.
  #[local] Set Default Proof Using "Hll".

  Local Notation wl := (wl_of ll).
  Local Notation W := (W (wl_of ll)).
  Local Notation NC := (NC ll).
  Local Notation LofS := (LofS ll).

  Lemma wl_of_length : length wl = 16%nat.
  Proof. unfold wl_of. rewrite map_length, seq_length. reflexivity. Qed.

  Lemma W_of : forall l, 0 <= l <= 15 -> W l = countz l ll.
  Proof.
    intros l Hl. unfold ItDefs.W, wl_of. rewrite nth_map_seq by lia. f_equal. lia.
  Qed.

  Lemma W_of_nonneg : forall l, 0 <= W l.
  Proof.
    intros l. unfold ItDefs.W. destruct (Nat.lt_ge_cases (Z.to_nat l) 16) as [H|H].
    - unfold wl_of. rewrite nth_map_seq by lia. apply countz_nonneg.
    - rewrite nth_overflow by (rewrite wl_of_length; lia). lia.
  Qed.

  Let HW := W_of_nonneg.
  Let HL := wl_of_length.

  Lemma LofS_range : forall s, 0 <= s < NC -> 0 <= LofS s <= 15.
  Proof.
    intros s Hs. unfold ItDefs.LofS. apply (Forall_nth (fun l => 0 <= l <= 15) ll); [exact Hll|]. unfold ItDefs.NC, zlength in Hs. lia.
  Qed.

  Lemma sel_countz : forall l n, (n <= length ll)%nat ->
    Z.of_nat (length (sel (fun s => LofS s =? l) n)) = countz l (firstn n ll).
  Proof.
    intros l n. induction n as [|n IH]; intros Hn.
    - cbn. reflexivity.
    - rewrite sel_S, app_length, Nat2Z.inj_add, IH by lia.
      rewrite countz_firstn_S by lia. unfold ItDefs.LofS. rewrite Nat2Z.id.
      rewrite (Z.eqb_sym (nth n ll 0) l). destruct (l =? nth n ll 0); cbn [length]; lia.
  Qed.

  Lemma syms_of_sel : forall l, syms_of ll l = sel (fun s => LofS s =? l) (length ll).
  Proof. intros l. unfold syms_of, sel, ItDefs.NC, zlength. rewrite Nat2Z.id. reflexivity. Qed.

  Lemma syms_of_length : forall l, Z.of_nat (length (syms_of ll l)) = countz l ll.
  Proof.
    intros l. rewrite syms_of_sel, sel_countz by lia. rewrite firstn_all. reflexivity.
  Qed.

  Lemma SYM_spec : forall l r, 0 <= r < countz l ll ->
    0 <= SYM ll l r < NC /\ LofS (SYM ll l r) = l /\ countz l (firstn (Z.to_nat (SYM ll l r)) ll) = r.
  Proof.
    intros l r Hr. unfold SYM. rewrite syms_of_sel.
    pose proof (syms_of_length l) as SL. rewrite syms_of_sel in SL.
    pose proof (sel_spec (fun s => LofS s =? l) (length ll) (Z.to_nat r) ltac:(lia)) as [A [B C]].
    cbn zeta in *. set (s := nth (Z.to_nat r) (sel (fun s => LofS s =? l) (length ll)) 0) in *.
    apply Z.eqb_eq in A. split; [unfold ItDefs.NC, zlength; lia|]. split; [exact A|].
    rewrite <- sel_countz by lia. lia.
  Qed.

  Lemma countz_firstn_lt : forall s, 0 <= s < NC ->
    countz (LofS s) (firstn (Z.to_nat s) ll) < countz (LofS s) ll.
  Proof.
    intros s Hs. unfold ItDefs.NC, zlength in Hs.
    pose proof (countz_firstn_S (LofS s) ll (Z.to_nat s) ltac:(lia)) as E.
    unfold ItDefs.LofS in E at 3. rewrite Z.eqb_refl in E.
    pose proof (countz_firstn_le (LofS s) ll (S (Z.to_nat s))). lia.
  Qed.

  Definition sidx (s : Z) : Z := OFF wl (LofS s) + countz (LofS s) (firstn (Z.to_nat s) ll).

  Lemma sidx_range : forall s, 0 <= s < NC -> LofS s <> 0 ->
    OFF wl (LofS s) <= sidx s < OFF wl (LofS s + 1) /\ 1 <= LofS s <= 15.
  Proof.
    intros s Hs Hnz. pose proof (LofS_range s Hs) as LR. unfold sidx.
    rewrite (OFF_step wl HW HL (LofS s)) by lia. rewrite W_of by lia.
    pose proof (countz_firstn_lt s Hs). pose proof (countz_nonneg (LofS s) (firstn (Z.to_nat s) ll)). lia.
  Qed.

  Lemma sidx_inj : forall s1 s2, 0 <= s1 < NC -> 0 <= s2 < NC -> LofS s1 <> 0 -> LofS s2 <> 0 ->
    sidx s1 = sidx s2 -> s1 = s2.
  Proof.
    intros s1 s2 H1 H2 N1 N2 E.
    pose proof (sidx_range s1 H1 N1) as [R1 L1]. pose proof (sidx_range s2 H2 N2) as [R2 L2].
    destruct (Z.eq_dec (LofS s1) (LofS s2)) as [EL|NL].
    -
      destruct (Z.lt_total s1 s2) as [LT|[EQ|GT]]; [|exact EQ|]; exfalso.
      + pose proof (countz_firstn_S (LofS s1) ll (Z.to_nat s1) ltac:(unfold ItDefs.NC, zlength in H1; lia)) as X.
        unfold ItDefs.LofS in X at 3. rewrite Z.eqb_refl in X.
        pose proof (countz_firstn_mono (LofS s1) ll (S (Z.to_nat s1)) (Z.to_nat s2) ltac:(lia)).
        unfold sidx in E. rewrite <- EL in E. lia.
      + pose proof (countz_firstn_S (LofS s2) ll (Z.to_nat s2) ltac:(unfold ItDefs.NC, zlength in H2; lia)) as X.
        unfold ItDefs.LofS in X at 3. rewrite Z.eqb_refl in X.
        pose proof (countz_firstn_mono (LofS s2) ll (S (Z.to_nat s2)) (Z.to_nat s1) ltac:(lia)).
        unfold sidx in E. rewrite EL in E. lia.
    - exfalso.
      destruct (Z.lt_total (LofS s1) (LofS s2)) as [LT|[EQ|GT]]; [|contradiction|].
      + pose proof (OFF_mono wl HW HL (LofS s1 + 1) (LofS s2) ltac:(lia)). lia.
      + pose proof (OFF_mono wl HW HL (LofS s2 + 1) (LofS s1) ltac:(lia)). lia.
  Qed.

  Lemma sidx_SYM : forall l r, 1 <= l <= 15 -> 0 <= r < W l -> sidx (SYM ll l r) = OFF wl l + r.
  Proof.
    intros l r Hl Hr. rewrite W_of in Hr by lia. pose proof (SYM_spec l r Hr) as [A [B C]].
    unfold sidx. rewrite B, C. reflexivity.
  Qed.

  Lemma In_sort_writes : forall i v,
    In (i, v) (sort_writes wl ll) <-> 0 <= v < NC /\ LofS v <> 0 /\ i = sidx v.
  Proof.
    intros i v. unfold sort_writes. rewrite in_flat_map. split.
    - intros [s [Hs Hin]]. apply in_map_iff in Hs as [n [<- Hn]]. apply in_seq in Hn.
      destruct (Z.eqb_spec (LofS (Z.of_nat n)) 0) as [E|E]; [destruct Hin|].
      destruct Hin as [Hin|[]]. injection Hin; intros <- <-.
      split; [unfold ItDefs.NC, zlength in *; lia|]. split; [exact E|]. unfold sidx. rewrite Nat2Z.id. reflexivity.
    - intros [Hv [Hnz ->]]. exists v. split.
      + apply in_map_iff. exists (Z.to_nat v). split; [lia|]. apply in_seq. unfold ItDefs.NC, zlength in *. lia.
      + destruct (Z.eqb_spec (LofS v) 0); [contradiction|]. left. reflexivity.
  Qed.

  Lemma sort_writes_range : forall i v, In (i, v) (sort_writes wl ll) -> 0 <= i < NZ wl /\ 0 <= v < NC.
  Proof.
    intros i v H. apply In_sort_writes in H as [Hv [Hnz ->]].
    pose proof (sidx_range v Hv Hnz) as [R L].
    pose proof (OFF_nonneg wl HW HL (LofS v)). pose proof (OFF_mono wl HW HL (LofS v + 1) 16 ltac:(lia)).
    unfold ItDefs.NZ. lia.
  Qed.

  Lemma sorted_cell : forall work l r, 1 <= l <= 15 -> 0 <= r < W l -> NZ wl <= arr_len work ->
    arr_get (applyw (sort_writes wl ll) work) (OFF wl l + r) = SYM ll l r.
  Proof.
    intros work l r Hl Hr Hlen.
    pose proof Hr as Hr'. rewrite W_of in Hr' by lia. pose proof (SYM_spec l r Hr') as [A [B C]].
    assert (Hin : In (OFF wl l + r, SYM ll l r) (sort_writes wl ll)).
    { apply In_sort_writes. split; [exact A|]. split; [rewrite B; lia|]. symmetry. apply sidx_SYM; assumption. }
    pose proof (sort_writes_range _ _ Hin) as [R _].
    apply (applyw_all (fun i v => i = OFF wl l + r -> v = SYM ll l r)); [| eapply in_map_fst; exact Hin | lia | reflexivity].
    intros j v Hj ->. apply In_sort_writes in Hj as [Hv [Hnz E]].
    apply sidx_inj; try assumption; [rewrite B; lia|]. rewrite <- E. symmetry. apply sidx_SYM; assumption.
  Qed.

  Lemma sorted_work : forall work k, NZ wl <= arr_len work -> 0 <= k < NZ wl ->
    arr_get (applyw (sort_writes wl ll) work) k = wsym wl ll k.
  Proof.
    intros work k Hlen Hk.
    pose proof (len_at_spec wl HW HL k Hk) as [L O]. pose proof (rank_at_spec wl HW HL k Hk) as R.
    unfold wsym. replace k with (OFF wl (len_at wl k) + rank_at wl k) at 1 by (unfold rank_at; lia).
    apply sorted_cell; assumption.
  Qed.

  Lemma wsym_spec : forall k, 0 <= k < NZ wl -> 0 <= wsym wl ll k < NC /\ LofS (wsym wl ll k) = len_at wl k.
  Proof.
    intros k Hk.
    pose proof (len_at_spec wl HW HL k Hk) as [L O]. pose proof (rank_at_spec wl HW HL k Hk) as R.
    rewrite W_of in R by lia. pose proof (SYM_spec (len_at wl k) (rank_at wl k) R) as [A [B C]].
    unfold wsym. split; assumption.
  Qed.

  Lemma sum_countz : forall xs, Forall (fun l => 0 <= l <= 15) xs ->
    sumz (fun l => countz l xs) 0 16 = zlength xs.
  Proof.
    intros xs Hxs. induction xs as [|x xs IH].
    - rewrite (@zlength_nil Z). apply sumz_zero. intros; reflexivity.
    - apply Forall_cons_iff in Hxs as [Hx Hxs]. rewrite zlength_cons, <- (IH Hxs).
      rewrite (sumz_ext (fun l => countz l (x :: xs)) (fun l => (if l =? x then 1 else 0) + countz l xs)) by (intros; apply countz_cons).
      rewrite sumz_add, sumz_indicator by lia.
      destruct (Z.leb_spec 0 x), (Z.ltb_spec x 16); cbn [andb]; lia.
  Qed.

  Lemma NZ_le_NC : NZ wl <= NC.
  Proof.
    unfold ItDefs.NZ, ItDefs.OFF, ItDefs.NC. rewrite <- (sum_countz ll Hll).
    rewrite (sumz_cons (fun l => countz l ll) 0 16) by lia.
    rewrite (sumz_ext (ItDefs.W wl) (fun l => countz l ll) 1 16) by (intros; apply W_of; lia).
    pose proof (countz_nonneg 0 ll). change (0 + 1) with 1. lia.
  Qed.

  Lemma sort_writes_untouched : forall work i, ~ (0 <= i < NZ wl) ->
    arr_get (applyw (sort_writes wl ll) work) i = arr_get work i.
  Proof.
    intros work i Hi. apply applyw_other. intros v Hin. apply sort_writes_range in Hin. lia.
  Qed.
End LL.
End ItSort.

Module ItSimPre.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ModelRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItMath.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItSort.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma lens_list_length : forall lens ofs codes, length (lens_list lens ofs codes) = Z.to_nat codes.
Proof. intros. unfold lens_list. rewrite map_length, seq_length. reflexivity. Qed.

Lemma LofS_lens : forall lens ofs codes s, 0 <= s < codes ->
  LofS (lens_list lens ofs codes) s = arr_get lens (ofs + s).
Proof.
  intros lens ofs codes s Hs. unfold LofS, lens_list. rewrite nth_map_seq by lia. f_equal. lia.
Qed.

Lemma nth_lens_list : forall lens ofs codes n, (n < Z.to_nat codes)%nat ->
  nth n (lens_list lens ofs codes) 0 = arr_get lens (ofs + Z.of_nat n).
Proof. intros. unfold lens_list. rewrite nth_map_seq by lia. reflexivity. Qed.

Lemma lens_list_Forall : forall lens ofs codes,
  (forall i, ofs <= i < ofs + codes -> 0 <= arr_get lens i <= 15) ->
  Forall (fun l => 0 <= l <= 15) (lens_list lens ofs codes).
Proof.
  intros lens ofs codes H. unfold lens_list. apply Forall_map. apply Forall_forall.
  intros n Hn. apply in_seq in Hn. apply H. lia.
Qed.

Lemma NC_lens : forall lens ofs codes, 0 <= codes -> NC (lens_list lens ofs codes) = codes.
Proof. intros. unfold NC, zlength. rewrite lens_list_length. lia. Qed.

Lemma arr_get_of_list_nth : forall l i, 0 <= i -> arr_get (arr_of_list l) i = nth (Z.to_nat i) l 0.
Proof.
  intros l i Hi. unfold arr_of_list, parr_of_list. rewrite (arr_get_upd l _ 0 i 0).
  unfold arr_inb. rewrite arr_len_make, arr_get_make. rewrite Z.sub_0_r.
  destruct (Z.ltb_spec i (0 + zlength l)).
  - destruct (Z.leb_spec 0 i); [|lia]. destruct (Z.ltb_spec i (zlength l)); [|lia]. reflexivity.
  - cbn [andb]. rewrite Bool.andb_false_r. symmetry. apply nth_overflow. unfold zlength in *. lia.
Qed.


Section Pre.
  Variable lens : arr.
Variable lens_ofs : Z.
Variable codes : Z.
Variable ll : list Z.
Variable wl : list Z.
  Hypothesis Hcodes : 0 <= codes <= 288.
  Hypothesis Hlens : forall i, lens_ofs <= i < lens_ofs + codes -> 0 <= arr_get lens i <= 15.
  Hypothesis Ell : ll = lens_list lens lens_ofs codes.
  Hypothesis Ewl : wl = wl_of ll.
  #[local] Set Default Proof Using "Hcodes Hlens Ell Ewl".

  Lemma Hll : Forall (fun l => 0 <= l <= 15) ll.
  Proof. rewrite Ell. apply lens_list_Forall. exact Hlens. Qed.
  Lemma HW : forall l, 0 <= W wl l.
  Proof. rewrite Ewl. apply (W_of_nonneg ll Hll). Qed.
  Lemma HL : length wl = 16%nat.
  Proof. rewrite Ewl. apply (wl_of_length ll Hll). Qed.
  Lemma W_count : forall l, 0 <= l <= 15 -> W wl l = countz l ll.
  Proof. rewrite Ewl. apply (W_of ll Hll). Qed.
  Lemma ll_length : length ll = Z.to_nat codes.
  Proof. rewrite Ell. apply lens_list_length. Qed.
  Lemma NC_ll : NC ll = codes.
  Proof. rewrite Ell. apply NC_lens. lia. Qed.
  Lemma nth_ll : forall n, (n < Z.to_nat codes)%nat -> nth n ll 0 = arr_get lens (lens_ofs + Z.of_nat n).
  Proof. rewrite Ell. apply nth_lens_list. Qed.
  Lemma LofS_ll : forall s, 0 <= s < codes -> LofS ll s = arr_get lens (lens_ofs + s).
  Proof. rewrite Ell. apply LofS_lens. Qed.

  Lemma NZ_le_codes : NZ wl <= codes.
  Proof. pose proof (NZ_le_NC ll Hll) as H. rewrite <- Ewl, NC_ll in H. exact H. Qed.

  Lemma zero_count_spec :
    arr_len (it_zero_count (arr_make 16 0)) = 16 /\ forall i, arr_get (it_zero_count (arr_make 16 0)) i = 0.
  Proof.
    unfold it_zero_count.
    apply (forZ_ind (fun _ a => arr_len a = 16 /\ forall i, arr_get a i = 0)).
    - intros i a Hi [L G]. split; [rewrite arr_len_set; exact L|].
      intros j. rewrite arr_get_set. destruct (_ && _); [reflexivity | apply G].
    - split; [apply arr_len_make | intros; apply arr_get_make].
    - unfold MAXBITS. lia.
  Qed.

  Definition CNT : arr := it_count lens lens_ofs codes (it_zero_count (arr_make 16 0)).

  Lemma count_spec : arr_len CNT = 16 /\ forall l, 0 <= l <= 15 -> arr_get CNT l = W wl l.
  Proof.
    unfold CNT, it_count. pose proof zero_count_spec as [ZL ZG].
    enough (H : arr_len (forZ 0 codes (fun sym cnt => let l := arr_get lens (lens_ofs + sym) in
                                                    arr_set cnt l (wrap16 (arr_get cnt l + 1)))
                              (it_zero_count (arr_make 16 0))) = 16 /\
                forall l, 0 <= l <= 15 ->
                  arr_get (forZ 0 codes (fun sym cnt => let l := arr_get lens (lens_ofs + sym) in
                                                         arr_set cnt l (wrap16 (arr_get cnt l + 1)))
                                (it_zero_count (arr_make 16 0))) l = countz l (firstn (Z.to_nat codes) ll)).
    { destruct H as [L G]. split; [exact L|]. intros l Hl. rewrite G by lia.
      rewrite <- ll_length, firstn_all. symmetry. apply W_count. lia. }
    apply (forZ_ind (fun sym c => arr_len c = 16 /\ forall l, 0 <= l <= 15 -> arr_get c l = countz l (firstn (Z.to_nat sym) ll))).
    - intros i c Hi [L G]. cbn zeta. split; [rewrite arr_len_set; exact L|].
      intros l Hl. pose proof (Hlens (lens_ofs + i) ltac:(lia)) as R.
      replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
      rewrite countz_firstn_S by (rewrite ll_length; lia).
      rewrite nth_ll by lia. rewrite Z2Nat.id by lia.
      rewrite arr_get_set. unfold arr_inb. rewrite L.
      rewrite G by lia.
      assert (B : 0 <= countz (arr_get lens (lens_ofs + i)) (firstn (Z.to_nat i) ll) <= i).
      { split; [apply countz_nonneg|].
        pose proof (countz_le_length (arr_get lens (lens_ofs + i)) (firstn (Z.to_nat i) ll)).
        unfold zlength in H. rewrite firstn_length, ll_length in H. lia. }
      rewrite wrap16_small by lia.
      destruct (Z.eqb_spec (arr_get lens (lens_ofs + i)) l) as [E|E].
      + rewrite <- E. destruct (Z.leb_spec 0 (arr_get lens (lens_ofs + i))); [|lia].
        destruct (Z.ltb_spec (arr_get lens (lens_ofs + i)) 16); [|lia]. cbn [andb]. rewrite Z.eqb_refl. lia.
      + cbn [andb]. rewrite G by lia. destruct (Z.eqb_spec l (arr_get lens (lens_ofs + i))); [congruence|]. lia.
    - split; [exact ZL|]. intros l Hl. rewrite ZG. change (firstn (Z.to_nat 0) ll) with (@nil Z). rewrite countz_nil. reflexivity.
    - lia.
  Qed.

  Section WithCount.
    Variable C : arr.
    Hypothesis HC : forall l, 0 <= l <= 15 -> arr_get C l = W wl l.
    #[local] Set Default Proof Using "Hcodes Hlens Ell Ewl HC".

    Lemma find_max_spec : it_find_max C = MAXL wl.
    Proof.
      pose proof (MAXL_spec wl HW HL) as [M1 [M2 M3]]. unfold it_find_max, MAXBITS.
      assert (G : forall m, MAXL wl <= m <= 15 -> forall fuel, m - MAXL wl + 1 <= fuel ->
                loopZ fuel (fun max => if (1 <=? max) && (arr_get C max =? 0) then (true, max - 1) else (false, max)) m = MAXL wl).
      { intros m Hm. remember (Z.to_nat (m - MAXL wl)) as n eqn:Hn. revert m Hm Hn.
        induction n as [|n IH]; intros m Hm Hn fuel Hf.
        - replace m with (MAXL wl) by lia. rewrite loopZ_step by lia.
          destruct (Z.leb_spec 1 (MAXL wl)); cbn [andb]; [|reflexivity].
          rewrite HC by lia. destruct (Z.eqb_spec (W wl (MAXL wl)) 0); [|reflexivity]. specialize (M3 ltac:(lia)). lia.
        - rewrite loopZ_step by lia. destruct (Z.leb_spec 1 m); [|lia]. rewrite HC by lia.
          rewrite M2 by lia. cbn [andb Z.eqb]. apply IH; lia. }
      apply G; lia.
    Qed.

    Lemma find_min_spec : 1 <= MAXL wl -> it_find_min C (MAXL wl) = MINL wl.
    Proof.
      intros HM. pose proof (MINL_spec wl HW HL HM) as [A [B D]]. pose proof (MAXL_spec wl HW HL) as [M0 _]. unfold it_find_min.
      assert (G : forall m, 1 <= m <= MINL wl -> forall fuel, MINL wl - m + 1 <= fuel ->
                loopZ fuel (fun min => if (min <? MAXL wl) && (arr_get C min =? 0) then (true, min + 1) else (false, min)) m = MINL wl).
      { intros m Hm. remember (Z.to_nat (MINL wl - m)) as n eqn:Hn. revert m Hm Hn.
        pose proof (MAXL_spec wl HW HL) as [M1 _].
        induction n as [|n IH]; intros m Hm Hn fuel Hf.
        - replace m with (MINL wl) by lia. rewrite loopZ_step by lia.
          destruct (Z.ltb_spec (MINL wl) (MAXL wl)); cbn [andb]; [|reflexivity].
          rewrite HC by lia. destruct (Z.eqb_spec (W wl (MINL wl)) 0); [lia|reflexivity].
        - rewrite loopZ_step by lia. destruct (Z.ltb_spec m (MAXL wl)); [|lia]. rewrite HC by lia.
          rewrite D by lia. cbn [andb Z.eqb]. apply IH; lia. }
      apply G; lia.
    Qed.

    Definition Lft (m : Z) : Z := 2 ^ m - sumz (fun l => W wl l * 2 ^ (m - l)) 1 (m + 1).

    Lemma Lft_0 : Lft 0 = 1.
    Proof. unfold Lft. rewrite sumz_nil by lia. reflexivity. Qed.

    Lemma Lft_S : forall m, 1 <= m -> Lft m = 2 * Lft (m - 1) - W wl m.
    Proof.
      intros m Hm. unfold Lft. rewrite (sumz_snoc _ 1 m) by lia. replace (m - 1 + 1) with m by lia.
      rewrite Z.sub_diag. change (2 ^ 0) with 1.
      rewrite (sumz_ext (fun l => W wl l * 2 ^ (m - l)) (fun l => (W wl l * 2 ^ (m - 1 - l)) * 2) 1 m).
      2:{ intros i Hi. rewrite <- Z.mul_assoc. f_equal. replace (m - i) with ((m - 1 - i) + 1) by lia. rewrite Z.pow_add_r by lia. reflexivity. }
      rewrite sumz_scale. replace m with ((m - 1) + 1) at 1 by lia. rewrite Z.pow_add_r by lia. lia.
    Qed.

    Lemma Lft_15 : Lft 15 = LEFT wl.
    Proof. unfold Lft, ItDefs.LEFT. change (15 + 1) with 16. reflexivity. Qed.

    Lemma Lft_neg_persist : forall m m', 0 <= m <= m' -> Lft m < 0 -> Lft m' < 0.
    Proof.
      intros m m' H Hneg. remember (Z.to_nat (m' - m)) as n eqn:Hn. revert m' H Hn.
      induction n as [|n IH]; intros m' H Hn.
      - replace m' with m by lia. exact Hneg.
      - rewrite (Lft_S m') by lia. pose proof (IH (m' - 1) ltac:(lia) ltac:(lia)). pose proof (HW m'). lia.
    Qed.

    Lemma left_check_spec : it_left_check C = (if LEFT wl <? 0 then None else Some (LEFT wl)).
    Proof.
      unfold it_left_check, MAXBITS.
      set (F := fun st : Z * Z => let '(len, lft) := st in
             if len <=? 15 then let lft0 := Z.shiftl lft 1 in let lft1 := lft0 - arr_get C len in
                                if lft1 <? 0 then inr None else inl (len + 1, lft1)
             else inr (Some lft)).
      assert (G : forall m v, 1 <= m <= 16 -> v = Lft (m - 1) -> 0 <= v -> forall fuel, 17 - m <= fuel ->
                iterZ fuel F (fun st => Some (snd st)) (m, v) = (if LEFT wl <? 0 then None else Some (LEFT wl))).
      { intros m v Hm. remember (Z.to_nat (16 - m)) as n eqn:Hn. revert m v Hm Hn.
        induction n as [|n IH]; intros m v Hm Hn Hv Hpos fuel Hf.
        - replace m with 16 in * by lia. rewrite iterZ_step by lia. unfold F at 1.
          destruct (Z.leb_spec 16 15); [lia|]. replace (16 - 1) with 15 in Hv by lia. rewrite Lft_15 in Hv. subst v.
          destruct (Z.ltb_spec (LEFT wl) 0); [lia|reflexivity].
        - rewrite iterZ_step by lia. unfold F at 1. destruct (Z.leb_spec m 15); [|lia].
          rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. rewrite HC by lia.
          assert (E : v * 2 - W wl m = Lft m) by (rewrite (Lft_S m) by lia; subst v; lia). rewrite E.
          destruct (Z.ltb_spec (Lft m) 0).
          + pose proof (Lft_neg_persist m 15 ltac:(lia) ltac:(lia)) as P15. rewrite Lft_15 in P15.
            destruct (Z.ltb_spec (LEFT wl) 0); [reflexivity|lia].
          + apply IH; try lia. f_equal. lia. }
      apply G; [lia| rewrite <- Lft_0; f_equal; lia | lia | lia].
    Qed.

    Definition OFS : arr := it_offs C (arr_make 16 0).

    Lemma offs_spec : arr_len OFS = 16 /\ forall l, 1 <= l <= 15 -> arr_get OFS l = OFF wl l.
    Proof.
      unfold OFS, it_offs, MAXBITS. pose proof NZ_le_codes as NZC.
      apply (forZ_ind (fun len o => arr_len o = 16 /\ forall l, 1 <= l <= len -> arr_get o l = OFF wl l)).
      - intros i o Hi [L G]. split; [rewrite arr_len_set; exact L|]. intros l Hl.
        rewrite arr_get_set. unfold arr_inb. rewrite L.
        destruct (Z.eqb_spec (i + 1) l) as [<-|NE].
        + destruct (Z.leb_spec 0 (i + 1)); [|lia]. destruct (Z.ltb_spec (i + 1) 16); [|lia]. cbn [andb].
          rewrite G, HC by lia. rewrite (OFF_step wl HW HL) by lia.
          pose proof (OFF_nonneg wl HW HL i). pose proof (HW i).
          pose proof (OFF_mono wl HW HL (i + 1) 16 ltac:(lia)) as M. rewrite (OFF_step wl HW HL) in M by lia.
          rewrite (NZ_eq wl HW HL) in NZC. apply wrap16_small. lia.
        + cbn [andb]. apply G. lia.
      - split; [rewrite arr_len_set; apply arr_len_make|]. intros l Hl. replace l with 1 by lia.
        rewrite arr_get_set_same by (rewrite arr_len_make; lia). symmetry. apply (OFF_1 wl HW HL).
      - lia.
    Qed.
  End WithCount.

  Definition SW (n : Z) : list (Z * Z) :=
    flat_map (fun s => let l := LofS ll s in
                       if l =? 0 then []
                       else [(OFF wl l + countz l (firstn (Z.to_nat s) ll), s)])
             (map Z.of_nat (seq 0 (Z.to_nat n))).

  Lemma SW_all : SW codes = sort_writes wl ll.
  Proof. unfold SW, sort_writes. rewrite NC_ll. reflexivity. Qed.

  Lemma SW_step : forall n, 0 <= n ->
    SW (n + 1) = SW n ++ (if LofS ll n =? 0 then [] else [(OFF wl (LofS ll n) + countz (LofS ll n) (firstn (Z.to_nat n) ll), n)]).
  Proof.
    intros n Hn. unfold SW. replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
    rewrite seq_S, map_app, flat_map_app. cbn [map flat_map Nat.add]. rewrite Z2Nat.id by lia.
    rewrite app_nil_r. reflexivity.
  Qed.

  Lemma sort_spec : forall (O : arr) (work : arr),
    arr_len O = 16 -> (forall l, 1 <= l <= 15 -> arr_get O l = OFF wl l) ->
    snd (it_sort lens lens_ofs codes (O, work)) = applyw (sort_writes wl ll) work.
  Proof.
    intros O work HOL HO. rewrite <- SW_all. unfold it_sort. pose proof NZ_le_codes as NZC. pose proof Hll as FL.
    enough (G : (fun sym ow =>
                   arr_len (fst ow) = 16 /\
                   (forall l, 1 <= l <= 15 -> arr_get (fst ow) l = OFF wl l + countz l (firstn (Z.to_nat sym) ll)) /\
                   snd ow = applyw (SW sym) work) codes
                (forZ 0 codes (fun sym ow => let '(offs, work0) := ow in
                   let l := arr_get lens (lens_ofs + sym) in
                   if negb (l =? 0) then
                     let o := arr_get offs l in (arr_set offs l (wrap16 (o + 1)), arr_set work0 o (wrap16 sym))
                   else (offs, work0)) (O, work))).
    { cbn beta in G. destruct G as [_ [_ G]]. exact G. }
    apply forZ_ind.
    - intros i [offs w] Hi [L [G E]]. cbn [fst snd] in L, G, E. cbn zeta.
      pose proof (Hlens (lens_ofs + i) ltac:(lia)) as R.
      rewrite <- (LofS_ll i) by lia.
      rewrite SW_step by lia. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
      rewrite <- (LofS_ll i) in R by lia.
      destruct (Z.eqb_spec (LofS ll i) 0) as [Z0|NZ0]; cbn [negb fst snd].
      + rewrite app_nil_r. split; [exact L|]. split; [|exact E]. intros l Hl.
        rewrite countz_firstn_S by (rewrite ll_length; lia). replace (nth (Z.to_nat i) ll 0) with (LofS ll i) by reflexivity. rewrite Z0.
        destruct (Z.eqb_spec l 0); [lia|]. rewrite G by lia. lia.
      + pose proof (sidx_range ll FL i ltac:(rewrite NC_ll; lia) NZ0) as [SR LR].
        unfold sidx in SR. rewrite <- Ewl in SR. rewrite <- G in SR by lia.
        pose proof (OFF_mono wl HW HL (LofS ll i + 1) 16 ltac:(lia)) as M. rewrite (NZ_eq wl HW HL) in NZC.
        pose proof (OFF_nonneg wl HW HL (LofS ll i)) as ON.
        split; [rewrite arr_len_set; exact L|]. split.
        * intros l Hl. rewrite arr_get_set. unfold arr_inb. rewrite L.
          rewrite countz_firstn_S by (rewrite ll_length; lia). replace (nth (Z.to_nat i) ll 0) with (LofS ll i) by reflexivity.
          destruct (Z.eqb_spec (LofS ll i) l) as [EQ|NE].
          -- rewrite <- EQ. destruct (Z.leb_spec 0 (LofS ll i)); [|lia]. destruct (Z.ltb_spec (LofS ll i) 16); [|lia]. cbn [andb].
             rewrite Z.eqb_refl. rewrite wrap16_small by lia. rewrite G by lia. lia.
          -- cbn [andb]. destruct (Z.eqb_spec l (LofS ll i)); [congruence|]. rewrite G by lia. lia.
        * rewrite applyw_snoc, <- E. rewrite G by lia. rewrite (wrap16_small i) by lia. reflexivity.
    - cbn [fst snd]. split; [exact HOL|]. split; [|reflexivity]. intros l Hl. rewrite HO by lia. change (firstn (Z.to_nat 0) ll) with (@nil Z). rewrite countz_nil. lia.
    - lia.
  Qed.
End Pre.
End ItSimPre.

Module ItSim1.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ModelRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItMath.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition fill_list (here incr base : Z) (m : nat) : list (Z * Z) :=
  map (fun j => (base + Z.of_nat j * incr, here)) (List.rev (seq 0 m)).

Lemma fill_list_S : forall here incr base m,
  fill_list here incr base (S m) = (base + Z.of_nat m * incr, here) :: fill_list here incr base m.
Proof.
  intros. unfold fill_list. rewrite seq_S, List.rev_app_distr. cbn [List.rev map app Nat.add]. reflexivity.
Qed.

Definition fill_stepf (here incr huff drop next : Z) (ft : Z * arr) : bool * (Z * arr) :=
  let '(fill, tbl) := ft in
  let fill := wrap32 (fill - incr) in
  let tbl := arr_set tbl (next + (Z.shiftr huff drop + fill)) here in
  if negb (fill =? 0) then (true, (fill, tbl)) else (false, (fill, tbl)).

Lemma it_fill_unfold : forall here incr huff drop next fill tbl,
  it_fill here incr huff drop next fill tbl = snd (loopZ fill (fill_stepf here incr huff drop next) (fill, tbl)).
Proof. reflexivity. Qed.

Lemma fill_stepf_eq : forall here incr huff drop next fill t,
  fill_stepf here incr huff drop next (fill, t) =
  (negb (wrap32 (fill - incr) =? 0), (wrap32 (fill - incr), arr_set t (next + (Z.shiftr huff drop + wrap32 (fill - incr))) here)).
Proof. intros. unfold fill_stepf. destruct (negb (wrap32 (fill - incr) =? 0)); reflexivity. Qed.

Lemma it_fill_loop : forall here incr huff drop next (m : nat) fuel t,
  1 <= incr -> (1 <= m)%nat -> Z.of_nat m * incr < 4294967296 -> Z.of_nat m <= fuel ->
  loopZ fuel (fill_stepf here incr huff drop next) (Z.of_nat m * incr, t)
  = (0, applyw (fill_list here incr (next + Z.shiftr huff drop) m) t).
Proof.
  intros here incr huff drop next m. induction m as [|m IH]; intros fuel t Hincr Hm Hb Hf; [lia|].
  rewrite loopZ_step by lia. rewrite fill_stepf_eq.
  replace (Z.of_nat (S m) * incr - incr) with (Z.of_nat m * incr) by lia.
  rewrite (wrap32_small (Z.of_nat m * incr)) by nia.
  rewrite fill_list_S, applyw_cons.
  replace (next + (Z.shiftr huff drop + Z.of_nat m * incr)) with (next + Z.shiftr huff drop + Z.of_nat m * incr) by lia.
  destruct m as [|m'].
  - cbn [Z.of_nat]. rewrite Z.mul_0_l. cbn [Z.eqb negb]. rewrite Z.add_0_r. reflexivity.
  - destruct (Z.eqb_spec (Z.of_nat (S m') * incr) 0); [nia|]. cbn [negb].
    apply IH; lia.
Qed.

Lemma it_fill_eq : forall here l huff drop next c t,
  0 <= l <= c -> c <= 15 -> 0 <= drop ->
  it_fill here (2 ^ l) huff drop next (2 ^ c) t =
  applyw (fill_list here (2 ^ l) (next + huff / 2 ^ drop) (Z.to_nat (2 ^ (c - l)))) t.
Proof.
  intros here l huff drop next c t Hl Hc Hd. rewrite it_fill_unfold.
  pose proof (pow2_le_15 l ltac:(lia)). pose proof (pow2_le_15 c ltac:(lia)). pose proof (pow2_le_15 (c - l) ltac:(lia)).
  assert (E : 2 ^ c = Z.of_nat (Z.to_nat (2 ^ (c - l))) * 2 ^ l).
  { rewrite Z2Nat.id by lia. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  rewrite E at 1 2. rewrite it_fill_loop; try lia.
  - cbn [snd]. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
  - rewrite Z2Nat.id by lia. nia.
Qed.


Fixpoint ib (w : nat) (h : Z) : Z :=
  if Z.odd (h / 2 ^ Z.of_nat w) then match w with O => 0 | S w' => ib w' h end
  else 2 ^ Z.of_nat w.

Definition ib_step (huff : Z) (incr : Z) : bool * Z :=
  if negb (Z.land huff incr =? 0) then (true, Z.shiftr incr 1) else (false, incr).

Lemma ib_loop : forall h w fuel, Z.of_nat w + 2 <= fuel ->
  loopZ fuel (ib_step h) (2 ^ Z.of_nat w) = ib w h.
Proof.
  intros h w. induction w as [|w IH]; intros fuel Hf.
  - rewrite loopZ_step by lia. unfold ib_step at 1.
    rewrite land_pow2_eq0 by lia. cbn [ib]. change (2 ^ Z.of_nat 0) with 1. rewrite !Z.div_1_r.
    destruct (Z.odd h); cbn [negb].
    + change (Z.shiftr 1 1) with 0. rewrite loopZ_step by lia. unfold ib_step at 1. rewrite Z.land_0_r. cbn [Z.eqb negb]. reflexivity.
    + reflexivity.
  - rewrite loopZ_step by lia. unfold ib_step at 1. rewrite land_pow2_eq0 by lia. cbn [ib].
    destruct (Z.odd (h / 2 ^ Z.of_nat (S w))); cbn [negb]; [|reflexivity].
    rewrite Z.shiftr_div_pow2 by lia. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    replace (2 * 2 ^ Z.of_nat w / 2 ^ 1) with (2 ^ Z.of_nat w) by (rewrite Z.mul_comm; apply eq_sym, Z.div_mul; lia).
    apply IH. lia.
Qed.

Lemma it_incr_back_ib : forall h len, 1 <= len <= 15 ->
  it_incr_back h len = ib (Z.to_nat (len - 1)) h.
Proof.
  intros h len Hl. unfold it_incr_back. rewrite shl32_pow2 by lia.
  replace (len - 1) with (Z.of_nat (Z.to_nat (len - 1))) at 1 by lia.
  apply (ib_loop h (Z.to_nat (len - 1)) 32). lia.
Qed.

Lemma ib_cases : forall w h, ib w h = 0 \/ exists p, 0 <= p <= Z.of_nat w /\ ib w h = 2 ^ p.
Proof.
  induction w as [|w IH]; intros h; cbn [ib].
  - destruct (Z.odd _); [left; reflexivity | right; exists 0; split; [lia|reflexivity]].
  - destruct (Z.odd _).
    + destruct (IH h) as [E|[p [Hp E]]]; [left; exact E | right; exists p; split; [lia| exact E]].
    + right. exists (Z.of_nat (S w)). split; [lia|reflexivity].
Qed.

Lemma ib_high : forall w r q, 0 <= r -> 0 <= q ->
  ib w (q * 2 ^ (Z.of_nat w + 1) + r) = ib w r.
Proof.
  induction w as [|w IH]; intros r q Hr Hq.
  - cbn [ib]. change (2 ^ Z.of_nat 0) with 1. change (Z.of_nat 0 + 1) with 1. rewrite Z.pow_1_r, !Z.div_1_r.
    replace (q * 2 + r) with (r + 2 * q) by lia. rewrite Z.odd_add_mul_2. reflexivity.
  - cbn [ib].
    assert (E : (q * 2 ^ (Z.of_nat (S w) + 1) + r) / 2 ^ Z.of_nat (S w) = r / 2 ^ Z.of_nat (S w) + 2 * q).
    { rewrite Z.pow_add_r, Z.pow_1_r by lia.
      replace (q * (2 ^ Z.of_nat (S w) * 2) + r) with (r + (q * 2) * 2 ^ Z.of_nat (S w)) by lia.
      rewrite Z.div_add by (apply Z.pow_nonzero; lia). lia. }
    rewrite E, Z.odd_add_mul_2.
    destruct (Z.odd (r / 2 ^ Z.of_nat (S w))); [|reflexivity].
    replace (q * 2 ^ (Z.of_nat (S w) + 1)) with ((q * 2) * 2 ^ (Z.of_nat w + 1)).
    2:{ rewrite Nat2Z.inj_succ. replace (Z.succ (Z.of_nat w) + 1) with ((Z.of_nat w + 1) + 1) by lia. rewrite (Z.pow_add_r 2 (Z.of_nat w + 1) 1) by lia. lia. }
    apply IH; lia.
Qed.

Lemma ib_rev : forall w c, 0 <= c < 2 ^ (Z.of_nat w + 1) ->
  let h := rev (Z.of_nat w + 1) c in
  (c + 1 < 2 ^ (Z.of_nat w + 1) -> ib w h <> 0 /\ Z.land h (ib w h - 1) + ib w h = rev (Z.of_nat w + 1) (c + 1)) /\
  (c + 1 = 2 ^ (Z.of_nat w + 1) -> ib w h = 0).
Proof.
  induction w as [|w IH]; intros c Hc; cbn zeta.
  - change (Z.of_nat 0 + 1) with 1 in *. change (2 ^ 1) with 2 in *.
    assert (c = 0 \/ c = 1) as [->| ->] by lia.
    + cbn. split; [intros _; split; [discriminate|reflexivity] | lia].
    + cbn. split; [lia | reflexivity].
  - set (W1 := Z.of_nat (S w) + 1) in *.
    assert (HW1 : W1 = (Z.of_nat w + 1) + 1) by (subst W1; lia).
    pose proof (Z.pow_nonneg 2 (Z.of_nat w + 1) ltac:(lia)) as P0.
    assert (P1 : 2 ^ W1 = 2 * 2 ^ (Z.of_nat w + 1)) by (rewrite HW1, Z.pow_add_r by lia; lia).
    pose proof (Z.mod_pos_bound c 2 ltac:(lia)) as Mc. pose proof (Z.div_mod c 2 ltac:(lia)) as Dc.
    assert (Hc2 : 0 <= c / 2 < 2 ^ (Z.of_nat w + 1)) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    assert (Eh : rev W1 c = (c mod 2) * 2 ^ (Z.of_nat w + 1) + rev (Z.of_nat w + 1) (c / 2)).
    { rewrite HW1. apply rev_S; lia. }
    pose proof (rev_bound (Z.of_nat w + 1) (c / 2) ltac:(lia)) as Rb.
    set (r := rev (Z.of_nat w + 1) (c / 2)) in *.
    assert (Etop : Z.odd (rev W1 c / 2 ^ Z.of_nat (S w)) = Z.odd c).
    { rewrite Eh. replace (Z.of_nat (S w)) with (Z.of_nat w + 1) by lia.
      rewrite Z.add_comm, Z.div_add by lia. rewrite (Z.div_small r) by lia. rewrite Z.add_0_l.
      rewrite Zmod_odd. destruct (Z.odd c); reflexivity. }
    cbn [ib]. rewrite Etop.
    destruct (Z.odd c) eqn:Hodd.
    +
      assert (Hm : c mod 2 = 1) by (rewrite Zmod_odd, Hodd; reflexivity).
      assert (Eib : ib w (rev W1 c) = ib w r).
      { rewrite Eh, Hm, Z.mul_1_l. rewrite <- (Z.mul_1_l (2 ^ (Z.of_nat w + 1))). apply ib_high; lia. }
      rewrite Eib. specialize (IH (c / 2) Hc2). cbn zeta in IH. fold r in IH. destruct IH as [IH1 IH2].
      split.
      * intros Hlt. assert (Hlt2 : c / 2 + 1 < 2 ^ (Z.of_nat w + 1)) by lia.
        destruct (IH1 Hlt2) as [NZ0 E]. split; [exact NZ0|].
        destruct (ib_cases w r) as [Z0|[p [Hp Ep]]]; [contradiction|]. rewrite Ep in *.
        assert (EL : Z.land (rev W1 c) (2 ^ p - 1) = Z.land r (2 ^ p - 1)).
        { rewrite !land_ones' by lia. rewrite Eh, Hm, Z.mul_1_l.
          rewrite (pow2_split (Z.of_nat w + 1) p) by lia. rewrite Z.add_comm, Z.mod_add; [reflexivity| apply Z.pow_nonzero; lia]. }
        rewrite EL, E. rewrite HW1. rewrite (rev_S (Z.of_nat w + 1) (c + 1)) by lia.
        replace ((c + 1) mod 2) with 0.
        2:{ replace (c + 1) with (0 + (c / 2 + 1) * 2) by lia. rewrite Z_mod_plus_full. reflexivity. }
        replace ((c + 1) / 2) with (c / 2 + 1).
        2:{ replace (c + 1) with ((c / 2 + 1) * 2) by lia. rewrite Z.div_mul by lia. reflexivity. }
        lia.
      * intros Heq. apply IH2. lia.
    +
      assert (Hm : c mod 2 = 0) by (rewrite Zmod_odd, Hodd; reflexivity).
      split.
      * intros Hlt. split; [apply Z.pow_nonzero; lia|].
        replace (Z.of_nat (S w)) with (Z.of_nat w + 1) by lia.
        rewrite land_ones' by lia. rewrite Eh, Hm, Z.mul_0_l, Z.add_0_l. rewrite (Z.mod_small r) by lia.
        rewrite HW1. rewrite (rev_S (Z.of_nat w + 1) (c + 1)) by lia.
        replace ((c + 1) mod 2) with 1.
        2:{ replace (c + 1) with (1 + (c / 2) * 2) by lia. rewrite Z_mod_plus_full. reflexivity. }
        replace ((c + 1) / 2) with (c / 2).
        2:{ replace (c + 1) with (c / 2 * 2 + 1) by lia. rewrite Z.div_add_l by lia. change (1 / 2) with 0. lia. }
        subst r. lia.
      * intros Heq. exfalso. lia.
Qed.

Lemma huff_update : forall len c, 1 <= len <= 15 -> 0 <= c < 2 ^ len ->
  (if negb (it_incr_back (rev len c) len =? 0)
   then Z.land (rev len c) (it_incr_back (rev len c) len - 1) + it_incr_back (rev len c) len
   else 0)
  = (if c + 1 <? 2 ^ len then rev len (c + 1) else 0).
Proof.
  intros len c Hl Hc. rewrite it_incr_back_ib by lia.
  pose proof (ib_rev (Z.to_nat (len - 1)) c) as B.
  replace (Z.of_nat (Z.to_nat (len - 1)) + 1) with len in B by lia.
  specialize (B Hc). cbn zeta in B. destruct B as [B1 B2].
  destruct (Z.ltb_spec (c + 1) (2 ^ len)).
  - destruct (B1 ltac:(lia)) as [NZ0 E]. destruct (Z.eqb_spec (ib (Z.to_nat (len - 1)) (rev len c)) 0); [contradiction|].
    cbn [negb]. exact E.
  - rewrite (B2 ltac:(lia)). reflexivity.
Qed.


Section Sub.
  Variable wl : list Z.
  Hypothesis HW : forall l, 0 <= W wl l.
  Hypothesis HL : length wl = 16%nat.
  Variable root : Z.
  Hypothesis Hroot : MINL wl <= root <= MAXL wl.
  Hypothesis HM1 : 1 <= MAXL wl.
  #[local] Set Default Proof Using "HW HL Hroot HM1".

  Local Notation W := (W wl).
  Local Notation MAXL := (MAXL wl).
  Local Notation TM := (TM wl).
  Local Notation len_at := (len_at wl).
  Local Notation rank_at := (rank_at wl).
  Local Notation Apos := (Apos wl).
  Local Notation NZ := (NZ wl).
  Local Notation GR := (GR wl root).
  Local Notation Pfx := (Pfx wl root).
  Local Notation cstar := (cstar wl root).

  Definition REM (k l : Z) : Z :=
    if l <? len_at k then 0 else if l =? len_at k then W l - rank_at k else W l.

  Definition sub_step (count : arr) (drop max : Z) (cl : Z * Z) : bool * (Z * Z) :=
    let '(curr, lft) := cl in
    if wrap32 (curr + drop) <? max then
      let lft := lft - arr_get count (wrap32 (curr + drop)) in
      if lft <=? 0 then (false, (curr, lft)) else (true, (wrap32 (curr + 1), Z.shiftl lft 1))
    else (false, (curr, lft)).

  Lemma subtable_curr_spec : forall count k, 0 <= k < NZ -> newtable wl root k = true ->
    (forall l, len_at k <= l <= 15 -> arr_get count l = REM k l) ->
    it_subtable_curr count (len_at k) root MAXL = cstar (Pfx k) (len_at k - root).
  Proof.
    intros count k Hk HN Hcnt.
    pose proof (root_range wl HW HL root Hroot HM1) as RR. pose proof (MAXL_spec wl HW HL) as [MM _].
    pose proof (newtable_long wl HW HL root Hroot HM1 k HN) as HLg. pose proof HLg as HLg'. unfold islong in HLg'. apply Z.ltb_lt in HLg'.
    pose proof (len_at_range wl HW HL k Hk) as LR. pose proof (rank_at_spec wl HW HL k Hk) as RK.
    pose proof (group_start wl HW HL root Hroot HM1 k Hk HN) as GS.
    pose proof (GR_pos wl HW HL root Hroot HM1) as GP.
    set (L := len_at k) in *. set (c0 := L - root).
    pose proof (cstar_spec wl HW HL root Hroot HM1 (Pfx k) c0 ltac:(lia)) as [C1 [C2 C3]].
    set (cs := cstar (Pfx k) c0) in *.
    set (RM := fun l => if l <? L then 0 else TM l - Apos k).
    assert (RM_step : forall c, c0 <= c <= MAXL - root ->
              arr_get count (root + c) * 2 ^ (MAXL - root - c) = RM (root + c) - RM (root + c - 1)).
    { intros c Hc. rewrite Hcnt by lia. unfold REM, RM. fold L.
      destruct (Z.ltb_spec (root + c) L); [lia|]. 
      destruct (Z.eqb_spec (root + c) L) as [E|NE].
      - destruct (Z.ltb_spec (root + c - 1) L); [|lia]. rewrite E.
        unfold ItDefs.Apos. fold L. rewrite (TM_step' wl HW HL L) by lia.
        replace (MAXL - root - c) with (MAXL - L) by lia. nia.
      - destruct (Z.ltb_spec (root + c - 1) L); [lia|].
        rewrite (TM_step' wl HW HL (root + c)) by lia. replace (MAXL - root - c) with (MAXL - (root + c)) by lia. nia. }
    assert (RM_c0 : RM (root + c0 - 1) = 0).
    { unfold RM. destruct (Z.ltb_spec (root + c0 - 1) L); [reflexivity|lia]. }
    assert (RM_TM : forall c, c0 <= c -> RM (root + c) = TM (root + c) - Apos k).
    { intros c Hc. unfold RM. destruct (Z.ltb_spec (root + c) L); [lia|reflexivity]. }
    assert (LOOP : forall c lft fuel, c0 <= c <= cs -> lft * 2 ^ (MAXL - root - c) = GR - RM (root + c - 1) ->
              cs - c + 1 <= fuel ->
              fst (loopZ fuel (sub_step count root MAXL) (c, lft)) = cs).
    { intros c lft fuel Hc. remember (Z.to_nat (cs - c)) as n eqn:Hn. revert c lft fuel Hc Hn.
      induction n as [|n IH]; intros c lft fuel Hc Hn Hinv Hf.
      - assert (c = cs) by lia. subst c. rewrite loopZ_step by lia. unfold sub_step at 1.
        replace (cs + root) with (root + cs) by lia. rewrite (wrap32_small (root + cs)) by lia.
        destruct (Z.ltb_spec (root + cs) MAXL); [|reflexivity].
        destruct C2 as [C2|C2]; [lia|].
        pose proof (RM_step cs ltac:(lia)) as RS. pose proof (RM_TM cs ltac:(lia)) as RT.
        pose proof (pow2_pos (MAXL - root - cs) ltac:(lia)) as PP.
        assert ((lft - arr_get count (root + cs)) * 2 ^ (MAXL - root - cs) <= 0).
        { rewrite Z.mul_sub_distr_r, RS, Hinv, RT, GS. lia. }
        destruct (Z.leb_spec (lft - arr_get count (root + cs)) 0); [reflexivity| nia].
      - rewrite loopZ_step by lia. unfold sub_step at 1.
        replace (c + root) with (root + c) by lia. rewrite (wrap32_small (root + c)) by lia.
        destruct (C3 c ltac:(lia)) as [D1 D2].
        destruct (Z.ltb_spec (root + c) MAXL); [|lia].
        pose proof (RM_step c ltac:(lia)) as RS. pose proof (RM_TM c ltac:(lia)) as RT.
        pose proof (pow2_pos (MAXL - root - c) ltac:(lia)) as PP.
        assert (HP : 0 < (lft - arr_get count (root + c)) * 2 ^ (MAXL - root - c)).
        { rewrite Z.mul_sub_distr_r, RS, Hinv, RT, GS. lia. }
        destruct (Z.leb_spec (lft - arr_get count (root + c)) 0); [nia|].
        cbn [fst]. rewrite (wrap32_small (c + 1)) by lia. apply IH; try lia.
        rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
        replace (root + (c + 1) - 1) with (root + c) by lia.
        rewrite <- Z.mul_assoc. replace (2 * 2 ^ (MAXL - root - (c + 1))) with (2 ^ (MAXL - root - c)).
        2:{ rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
        rewrite Z.mul_sub_distr_r, RS, Hinv. lia. }
    unfold it_subtable_curr. fold L. rewrite (wrap32_small (L - root)) by lia.
    pose proof (pow2_le_15 (L - root) ltac:(lia)).
    rewrite swrap32_small by (rewrite Z.shiftl_1_l; lia). rewrite Z.shiftl_1_l.
    change (fst (loopZ 16 (sub_step count root MAXL) (L - root, 2 ^ (L - root))) = cs).
    apply LOOP; [lia| |lia].
    fold c0. rewrite RM_c0, <- Z.pow_add_r by lia. unfold ItDefs.GR. rewrite Z.sub_0_r. f_equal. lia.
  Qed.
End Sub.
End ItSim1.

Module ItSim2.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ModelRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItMath.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItSort.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItSimPre.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItSim1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Trip.
  Variable ty : codetype.
Variable lens : arr.
Variable lens_ofs : Z.
Variable codes : Z.
Variable ll : list Z.
Variable wl : list Z.
Variable table : Z.
Variable root : Z.
  Hypothesis Hcodes : 0 <= codes <= 288.
  Hypothesis Hlens : forall i, lens_ofs <= i < lens_ofs + codes -> 0 <= arr_get lens i <= 15.
  Hypothesis Ell : ll = lens_list lens lens_ofs codes.
  Hypothesis Ewl : wl = wl_of ll.
  Hypothesis Hroot : MINL wl <= root <= MAXL wl.
  Hypothesis HM1 : 1 <= MAXL wl.
  Hypothesis HK : TM wl (MAXL wl) <= 2 ^ MAXL wl.
  Hypothesis Hty : ty = CODES -> codes <= 19.
  #[local] Set Default Proof Using "Hcodes Hlens Ell Ewl Hroot HM1 HK Hty".

  Let HW := HW lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl.
  Let HL := HL lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl.

  Local Notation W := (W wl).
  Local Notation NZ := (NZ wl).
  Local Notation MAXL := (MAXL wl).
  Local Notation len_at := (len_at wl).
  Local Notation rank_at := (rank_at wl).
  Local Notation code := (code wl).
  Local Notation hf := (hf wl).
  Local Notation Pfx := (Pfx wl root).
  Local Notation islong := (islong wl root).
  Local Notation newtable := (newtable wl root).
  Local Notation noff := (noff wl root).
  Local Notation curr := (curr wl root).
  Local Notation used := (used wl root).
  Local Notation drop := (drop wl root).
  Local Notation low := (low wl root).
  Local Notation wsym := (wsym wl ll).
  Local Notation REM := (REM wl).

  Definition X : ItCtx := mkItCtx ty lens lens_ofs table root MAXL (2 ^ root - 1).

  Definition StM (k : Z) (st : ItSt) : Prop :=
    t_huff st = hf k /\ t_sym st = k /\ t_len st = len_at k /\
    t_next st = table + noff k /\ t_curr st = curr k /\ t_drop st = drop k /\
    t_low st = low k /\ t_used st = used k /\
    arr_len (t_count st) = 16 /\
    (forall l, 1 <= l <= 15 -> arr_get (t_count st) l = REM k l) /\
    (forall j, 0 <= j < NZ -> arr_get (t_work st) j = wsym j).

  Let Hll' := ItSimPre.Hll lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl.

  Lemma wsym_facts : forall k, 0 <= k < NZ -> 0 <= wsym k < codes /\ LofS ll (wsym k) = len_at k.
  Proof.
    intros k Hk. pose proof (wsym_spec ll Hll' k) as WS. rewrite <- Ewl in WS.
    rewrite (NC_ll lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) in WS. apply WS. exact Hk.
  Qed.

  Lemma entry_eq : forall work k, 0 <= k < NZ ->
    (if wsym k + 1 <? it_match ty then (0, wsym k)
     else if it_match ty <=? wsym k
          then (wrap8 (it_extra ty work (wsym k - it_match ty)), it_base ty work (wsym k - it_match ty))
          else (96, 0)) = entry ty (wsym k).
  Proof.
    intros work k Hk. pose proof (wsym_facts k Hk) as [R _].
    destruct ty; cbn [it_match it_extra it_base entry].
    - specialize (Hty eq_refl). destruct (Z.ltb_spec (wsym k + 1) 20); [reflexivity|lia].
    - destruct (Z.ltb_spec (wsym k + 1) 257); [reflexivity|].
      destruct (Z.leb_spec 257 (wsym k)); [|reflexivity].
      unfold lext_a, lbase_a. rewrite !arr_get_of_list_nth by lia. reflexivity.
    - destruct (Z.ltb_spec (wsym k + 1) 0); [lia|]. destruct (Z.leb_spec 0 (wsym k)); [|lia].
      unfold dext_a, dbase_a. rewrite Z.sub_0_r. rewrite !arr_get_of_list_nth by lia. reflexivity.
  Qed.

  Lemma hf_step : forall k, 0 <= k < NZ ->
    (if negb (it_incr_back (hf k) (len_at k) =? 0)
     then Z.land (hf k) (it_incr_back (hf k) (len_at k) - 1) + it_incr_back (hf k) (len_at k)
     else 0) = hf (k + 1).
  Proof.
    intros k Hk. rewrite (hf_spec wl HW HL HK k Hk).
    pose proof (len_at_spec wl HW HL k Hk) as [L _]. pose proof (code_nonneg wl HW HL k Hk).
    pose proof (code_bound wl HW HL HK k Hk).
    rewrite huff_update by lia.
    unfold ItDefs.hf. destruct (Z.eqb_spec (k + 1) 0); [lia|]. replace (k + 1 - 1) with k by lia. reflexivity.
  Qed.

  Lemma REM_self : forall k, 0 <= k < NZ -> REM k (len_at k) = W (len_at k) - rank_at k.
  Proof. intros k Hk. unfold ItSim1.REM. rewrite Z.ltb_irrefl, Z.eqb_refl. reflexivity. Qed.

  Lemma cnt_step : forall cnt k, 0 <= k -> k + 1 < NZ -> arr_len cnt = 16 ->
    (forall l, 1 <= l <= 15 -> arr_get cnt l = REM k l) ->
    forall l, 1 <= l <= 15 -> arr_get (arr_set cnt (len_at k) (W (len_at k) - rank_at k - 1)) l = REM (k + 1) l.
  Proof.
    intros cnt k Hk Hk1 HLc Hc l Hl. pose proof (len_at_spec wl HW HL k ltac:(lia)) as [L1 _].
    rewrite arr_get_set. unfold arr_inb. rewrite HLc.
    destruct (len_at_step wl HW HL k Hk Hk1) as [[A [B C]]|[A [B [C D]]]]; unfold ItSim1.REM; rewrite ?B, ?C.
    - destruct (Z.eqb_spec (len_at k) l) as [<-|NE].
      + destruct (Z.leb_spec 0 (len_at k)); [|lia]. destruct (Z.ltb_spec (len_at k) 16); [|lia]. cbn [andb].
        rewrite Z.ltb_irrefl, Z.eqb_refl. lia.
      + cbn [andb]. rewrite Hc by lia. unfold ItSim1.REM.
        destruct (Z.ltb_spec l (len_at k)), (Z.eqb_spec l (len_at k)); try lia; reflexivity.
    - destruct (Z.eqb_spec (len_at k) l) as [<-|NE].
      + destruct (Z.leb_spec 0 (len_at k)); [|lia]. destruct (Z.ltb_spec (len_at k) 16); [|lia]. cbn [andb].
        destruct (Z.ltb_spec (len_at k) (len_at (k + 1))); [|lia]. lia.
      + cbn [andb]. rewrite Hc by lia. unfold ItSim1.REM.
        destruct (Z.ltb_spec l (len_at k)), (Z.eqb_spec l (len_at k)), (Z.ltb_spec l (len_at (k + 1))), (Z.eqb_spec l (len_at (k + 1))); try lia; try reflexivity.
        all: try (rewrite D by lia; reflexivity). all: subst; lia.
  Qed.

  Lemma low_val : forall k, 0 <= k < NZ -> islong k = true -> Z.land (hf k) (2 ^ root - 1) = rev root (Pfx k).
  Proof.
    intros k Hk HLg. pose proof (root_range wl HW HL root Hroot HM1) as RR.
    pose proof HLg as HLg'. unfold ItDefs.islong in HLg'. apply Z.ltb_lt in HLg'.
    rewrite (hf_spec wl HW HL HK k Hk). rewrite land_ones' by lia.
    pose proof (len_at_spec wl HW HL k Hk) as [L _]. pose proof (code_nonneg wl HW HL k Hk).
    rewrite rev_mod by lia. rewrite (Pfx_code wl HW HL root Hroot HM1 k Hk HLg). reflexivity.
  Qed.

  Lemma newtable_test : forall k, 0 <= k -> k + 1 < NZ ->
    (root <? len_at (k + 1)) && negb (Z.land (hf (k + 1)) (2 ^ root - 1) =? low k) = newtable (k + 1).
  Proof.
    intros k Hk Hk1. pose proof (root_range wl HW HL root Hroot HM1) as RR.
    unfold ItDefs.newtable. replace (k + 1 - 1) with k by lia.
    destruct (islong (k + 1)) eqn:HL1.
    2:{ unfold ItDefs.islong in HL1. rewrite HL1. reflexivity. }
    pose proof HL1 as HL1'. unfold ItDefs.islong in HL1'. rewrite HL1'. cbn [andb].
    rewrite (low_val (k + 1)) by (lia || exact HL1).
    pose proof (rev_bound root (Pfx (k + 1)) ltac:(lia)) as RB.
    pose proof (Pfx_bound wl HW HL root Hroot HM1 HK (k + 1) ltac:(lia)). pose proof (Pfx_nonneg wl HW HL root Hroot HM1 (k + 1) ltac:(lia)).
    unfold ItDefs.low. destruct (islong k) eqn:HL0; cbn [negb orb].
    - pose proof (Pfx_bound wl HW HL root Hroot HM1 HK k ltac:(lia)). pose proof (Pfx_nonneg wl HW HL root Hroot HM1 k ltac:(lia)).
      destruct (Z.eqb_spec (Pfx (k + 1)) (Pfx k)) as [E|NE].
      + rewrite E, Z.eqb_refl. reflexivity.
      + destruct (Z.eqb_spec (rev root (Pfx (k + 1))) (rev root (Pfx k))) as [E2|NE2]; [|reflexivity].
        exfalso. apply NE. apply (rev_inj root); lia || exact E2.
    - pose proof (pow2_le_15 root ltac:(lia)). destruct (Z.eqb_spec (rev root (Pfx (k + 1))) 4294967295); [lia|reflexivity].
  Qed.

  Lemma drop0_root : forall k, (if drop k =? 0 then root else drop k) = root.
  Proof.
    intros k. pose proof (root_range wl HW HL root Hroot HM1). unfold ItDefs.drop.
    destruct (islong k); [destruct (Z.eqb_spec root 0); lia | rewrite Z.eqb_refl; reflexivity].
  Qed.

  Lemma drop_low_new : forall k, newtable (k + 1) = true ->
    drop (k + 1) = root /\ low (k + 1) = rev root (Pfx (k + 1)).
  Proof.
    intros k HN. pose proof (newtable_long wl HW HL root Hroot HM1 (k + 1) HN) as HLg.
    unfold ItDefs.drop, ItDefs.low. rewrite HLg. split; reflexivity.
  Qed.

  Lemma drop_low_same : forall k, 0 <= k -> k + 1 < NZ -> newtable (k + 1) = false ->
    drop (k + 1) = drop k /\ low (k + 1) = low k.
  Proof.
    intros k Hk Hk1 HN. unfold ItDefs.drop, ItDefs.low. destruct (islong (k + 1)) eqn:HL1.
    - destruct (not_newtable wl HW HL root Hroot HM1 k Hk Hk1 HN HL1) as [HL0 HP]. rewrite HL0, HP. split; reflexivity.
    - destruct (islong k) eqn:HL0; [|split; reflexivity].
      rewrite (islong_mono wl HW HL root Hroot HM1 k (k + 1) ltac:(lia) Hk1 HL0) in HL1. discriminate HL1.
  Qed.

  Lemma used_bnd : forall k, 0 <= k < NZ -> 0 <= used k <= 32768 * (k + 1).
  Proof.
    intros k Hk. pose proof (root_range wl HW HL root Hroot HM1) as RR.
    remember (Z.to_nat k) as n eqn:Hn. revert k Hk Hn.
    induction n as [|n IH]; intros k Hk Hn.
    - replace k with 0 by lia. unfold ItDefs.used. rewrite (lay_0 wl HW HL root Hroot HM1). cbn [snd]. pose proof (pow2_le_15 root ltac:(lia)). lia.
    - specialize (IH (k - 1) ltac:(lia) ltac:(lia)). replace k with (k - 1 + 1) by lia.
      destruct (newtable (k - 1 + 1)) eqn:HN.
      + pose proof (lay_S_new wl HW HL root Hroot HM1 (k - 1) ltac:(lia) HN) as [_ [_ E]]. rewrite E.
        pose proof (curr_range wl HW HL root Hroot HM1 (k - 1 + 1) ltac:(lia)) as [C _].
        pose proof (pow2_le_15 (curr (k - 1 + 1)) ltac:(lia)). lia.
      + pose proof (lay_same_proj wl HW HL root Hroot HM1 (k - 1) ltac:(lia) HN) as [_ [_ E]]. rewrite E. lia.
  Qed.

  Lemma fill_writes_eq : forall k,
    fill_writes wl ll root ty table k =
    fill_list (here wl ll root ty k) (2 ^ (len_at k - drop k)) (table + noff k + hf k / 2 ^ drop k)
              (Z.to_nat (2 ^ (curr k - (len_at k - drop k)))).
  Proof. intros k. reflexivity. Qed.

  Ltac redst := cbv beta iota zeta delta [t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_min t_count t_tbl t_work
                                          x_ty x_lens x_lens_ofs x_table x_root x_max x_mask X].

  Lemma trip_tail : forall k LEN cnt' tbl work, 0 <= k -> k + 1 < NZ -> LEN = len_at (k + 1) ->
    arr_len cnt' = 16 -> (forall l, 1 <= l <= 15 -> arr_get cnt' l = REM (k + 1) l) ->
    (forall j, 0 <= j < NZ -> arr_get work j = wsym j) ->
    match
      (if (root <? LEN) && negb (Z.land (hf (k + 1)) (2 ^ root - 1) =? low k)
       then
        if it_not_enough ty
             (wrap32 (used k + Z.shiftl 1 (it_subtable_curr cnt' (LEN) (if drop k =? 0 then root else drop k) MAXL)))
        then
         ItFail
           {| t_huff := hf (k + 1); t_sym := k + 1; t_len := LEN;
              t_next := table + noff k + 2 ^ curr k;
              t_curr := it_subtable_curr cnt' (LEN) (if drop k =? 0 then root else drop k) MAXL;
              t_drop := if drop k =? 0 then root else drop k;
              t_low := low k;
              t_used := wrap32 (used k + Z.shiftl 1 (it_subtable_curr cnt' (LEN) (if drop k =? 0 then root else drop k) MAXL));
              t_min := 2 ^ curr k; t_count := cnt';
              t_tbl := applyw (fill_writes wl ll root ty table k) tbl; t_work := work |}
        else
         ItCont
           {| t_huff := hf (k + 1); t_sym := k + 1; t_len := LEN;
              t_next := table + noff k + 2 ^ curr k;
              t_curr := it_subtable_curr cnt' (LEN) (if drop k =? 0 then root else drop k) MAXL;
              t_drop := if drop k =? 0 then root else drop k;
              t_low := Z.land (hf (k + 1)) (2 ^ root - 1);
              t_used := wrap32 (used k + Z.shiftl 1 (it_subtable_curr cnt' (LEN) (if drop k =? 0 then root else drop k) MAXL));
              t_min := 2 ^ curr k; t_count := cnt';
              t_tbl := arr_set (applyw (fill_writes wl ll root ty table k) tbl)
                         (table + Z.land (hf (k + 1)) (2 ^ root - 1))
                         (code_pack (it_subtable_curr cnt' (LEN) (if drop k =? 0 then root else drop k) MAXL)
                                    root (table + noff k + 2 ^ curr k - table));
              t_work := work |}
       else
        ItCont
          {| t_huff := hf (k + 1); t_sym := k + 1; t_len := LEN;
             t_next := table + noff k; t_curr := curr k; t_drop := drop k; t_low := low k; t_used := used k;
             t_min := 2 ^ curr k; t_count := cnt';
             t_tbl := applyw (fill_writes wl ll root ty table k) tbl; t_work := work |})
    with
    | ItCont st' => k + 1 < NZ /\ fails_at wl root ty k = false /\ StM (k + 1) st' /\
                    t_tbl st' = applyw (trip_writes wl ll root ty table k) tbl /\ t_work st' = work
    | ItBreak st' => k + 1 = NZ /\ t_huff st' = hf NZ /\ t_len st' = len_at k /\ t_drop st' = drop k /\
                     t_next st' = table + noff k /\ t_used st' = used k /\
                     t_tbl st' = applyw (fill_writes wl ll root ty table k) tbl /\ t_work st' = work
    | ItFail st' => k + 1 < NZ /\ fails_at wl root ty k = true /\
                    t_tbl st' = applyw (fill_writes wl ll root ty table k) tbl /\ t_work st' = work
    end.
  Proof.
    intros k LEN cnt' tbl work Hk Hk1 ELEN Lc' Hc' Hw. subst LEN. pose proof (root_range wl HW HL root Hroot HM1) as RR.
    rewrite (newtable_test k Hk Hk1). rewrite drop0_root.
    unfold ItDefs.fails_at, ItDefs.trip_writes, ItDefs.link_writes.
    destruct (Z.ltb_spec (k + 1) NZ); [|lia]. cbn [andb].
    destruct (newtable (k + 1)) eqn:HN; cbn [andb].
    -
      pose proof (lay_S_new wl HW HL root Hroot HM1 k Hk HN) as [En [Ecu Eus]].
      pose proof (drop_low_new k HN) as [Edr Elo].
      pose proof (newtable_long wl HW HL root Hroot HM1 (k + 1) HN) as HLg.
      rewrite (subtable_curr_spec wl HW HL root Hroot HM1 cnt' (k + 1) ltac:(lia) HN) by (intros; apply Hc'; pose proof (len_at_spec wl HW HL (k + 1) ltac:(lia)); lia).
      rewrite <- Ecu.
      pose proof (curr_range wl HW HL root Hroot HM1 (k + 1) ltac:(lia)) as [C1 _].
      pose proof (used_bnd k ltac:(lia)) as UB. pose proof (NZ_le_codes lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) as NZC.
      pose proof (pow2_le_15 (curr (k + 1)) ltac:(lia)).
      rewrite Z.shiftl_1_l. rewrite (wrap32_small (used k + 2 ^ curr (k + 1))) by nia.
      rewrite <- Eus. rewrite (low_val (k + 1) ltac:(lia) HLg).
      destruct (it_not_enough ty (used (k + 1))) eqn:NE; cbn [negb].
      + cbn [t_tbl t_work]. repeat split; try reflexivity; lia.
      + split; [lia|]. split; [reflexivity|]. split.
        * unfold StM. cbn [t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_count t_work].
          rewrite En, Edr, Elo. repeat split; try reflexivity; try assumption; lia.
        * cbn [t_tbl t_work]. split; [|reflexivity]. rewrite applyw_snoc. rewrite En.
          replace (table + (noff k + 2 ^ curr k) - table) with (noff k + 2 ^ curr k) by lia.
          replace (table + noff k + 2 ^ curr k - table) with (noff k + 2 ^ curr k) by lia. reflexivity.
    -
      pose proof (lay_same_proj wl HW HL root Hroot HM1 k Hk HN) as [En [Ecu Eus]].
      pose proof (drop_low_same k Hk Hk1 HN) as [Edr Elo].
      split; [lia|]. split; [reflexivity|]. split.
      + unfold StM. cbn [t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_count t_work].
        rewrite En, Ecu, Eus, Edr, Elo. repeat split; try reflexivity; try assumption; lia.
      + cbn [t_tbl t_work]. rewrite app_nil_r. split; reflexivity.
  Qed.

  Lemma trip_spec : forall k st, 0 <= k < NZ -> StM k st ->
    match it_step X st with
    | ItBreak st' => k + 1 = NZ /\ t_huff st' = hf NZ /\ t_len st' = len_at k /\ t_drop st' = drop k /\
                     t_next st' = table + noff k /\ t_used st' = used k /\
                     t_tbl st' = applyw (fill_writes wl ll root ty table k) (t_tbl st) /\ t_work st' = t_work st
    | ItFail st' => k + 1 < NZ /\ fails_at wl root ty k = true /\
                    t_tbl st' = applyw (fill_writes wl ll root ty table k) (t_tbl st) /\ t_work st' = t_work st
    | ItCont st' => k + 1 < NZ /\ fails_at wl root ty k = false /\ StM (k + 1) st' /\
                    t_tbl st' = applyw (trip_writes wl ll root ty table k) (t_tbl st) /\ t_work st' = t_work st
    end.
  Proof.
    intros k st Hk SM. pose proof (root_range wl HW HL root Hroot HM1) as RR. pose proof (MAXL_spec wl HW HL) as [MM _].
    destruct st as [huff sym len next cur drp lw usd mn cnt tbl work].
    destruct SM as (Eh & Es & El & En & Ec & Ed & Elw & Eu & Lc & Hc & Hw). cbn [t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_count t_work] in *.
    subst huff sym len next cur drp lw usd.
    pose proof (len_at_spec wl HW HL k Hk) as [L1 _]. pose proof (len_at_range wl HW HL k Hk) as LR.
    pose proof (rank_at_spec wl HW HL k Hk) as RK. pose proof (curr_range wl HW HL root Hroot HM1 k Hk) as [CR1 [CR2 CR3]].
    pose proof (used_bnd k Hk) as UB. pose proof (NZ_le_codes lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) as NZC.
    assert (Hdrop : 0 <= drop k <= root) by (unfold ItDefs.drop; destruct (islong k); lia).
    assert (WB : W (len_at k) <= NZ).
    { pose proof (OFF_mono wl HW HL (len_at k + 1) 16 ltac:(lia)) as M. rewrite (OFF_step wl HW HL) in M by lia.
      pose proof (OFF_nonneg wl HW HL (len_at k)). rewrite <- (NZ_eq wl HW HL) in M. lia. }
    unfold it_step. redst.
    rewrite (Hw k Hk). rewrite (entry_eq work k Hk).
    destruct (entry ty (wsym k)) as [eop eval] eqn:Eent. redst.
    rewrite (wrap32_small (k + 1)) by lia.
    rewrite (Hc (len_at k)) by lia. rewrite (REM_self k Hk).
    rewrite (wrap16_small (W (len_at k) - rank_at k - 1)) by lia.
    rewrite (hf_step k Hk).
    rewrite (wrap8_small (len_at k - drop k)) by lia.
    rewrite !shl32_pow2 by lia.
    rewrite it_fill_eq by lia.
    assert (Etbl : applyw (fill_list (code_pack eop (len_at k - drop k) eval) (2 ^ (len_at k - drop k))
                             (table + noff k + hf k / 2 ^ drop k) (Z.to_nat (2 ^ (curr k - (len_at k - drop k))))) tbl
                   = applyw (fill_writes wl ll root ty table k) tbl).
    { rewrite fill_writes_eq. unfold ItDefs.here. rewrite Eent. reflexivity. }
    rewrite Etbl. clear Etbl.
    pose proof (last_iff wl HW HL k Hk) as LI.
    destruct (Z.eqb_spec (W (len_at k) - rank_at k - 1) 0) as [Hc0|Hc0];
      destruct (Z.eqb_spec (len_at k) MAXL) as [HlM|HlM]; cbn [andb negb].
    -
      assert (Hk1 : k + 1 = NZ) by (apply proj2 in LI; specialize (LI ltac:(lia)); lia).
      redst. rewrite Hk1. repeat split; reflexivity.
    -
      assert (Hk1 : k + 1 < NZ) by (destruct (Z.eq_dec k (NZ - 1)) as [E|E]; [apply proj1 in LI; specialize (LI E); lia | lia]).
      rewrite (Hw (k + 1)) by lia. pose proof (wsym_facts (k + 1) ltac:(lia)) as [WR WL].
      rewrite <- (LofS_ll lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) by lia.
      apply trip_tail; [lia | lia | exact WL | rewrite arr_len_set; exact Lc | apply cnt_step; try lia; assumption | exact Hw].
    - assert (Hk1 : k + 1 < NZ) by (destruct (Z.eq_dec k (NZ - 1)) as [E|E]; [apply proj1 in LI; specialize (LI E); lia | lia]).
      destruct (len_at_step wl HW HL k ltac:(lia) Hk1) as [[A [B C]]|[A _]]; [|lia].
      apply trip_tail; [lia | lia | exact (eq_sym B) | rewrite arr_len_set; exact Lc | apply cnt_step; try lia; assumption | exact Hw].
    - assert (Hk1 : k + 1 < NZ) by (destruct (Z.eq_dec k (NZ - 1)) as [E|E]; [apply proj1 in LI; specialize (LI E); lia | lia]).
      destruct (len_at_step wl HW HL k ltac:(lia) Hk1) as [[A [B C]]|[A _]]; [|lia].
      apply trip_tail; [lia | lia | exact (eq_sym B) | rewrite arr_len_set; exact Lc | apply cnt_step; try lia; assumption | exact Hw].
  Qed.
  Lemma trips_writes_S : forall n, 0 <= n ->
    trips_writes wl ll root ty table (n + 1) = trips_writes wl ll root ty table n ++ trip_writes wl ll root ty table n.
  Proof.
    intros n Hn. unfold ItDefs.trips_writes. replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
    rewrite seq_S, flat_map_app. cbn [flat_map Nat.add]. rewrite app_nil_r, Z2Nat.id by lia. reflexivity.
  Qed.

  Lemma trip_writes_nolink : forall k,
    link_writes wl root ty table k = [] -> trip_writes wl ll root ty table k = fill_writes wl ll root ty table k.
  Proof. intros k H. unfold ItDefs.trip_writes. rewrite H. apply app_nil_r. Qed.

  Definition loopF (st : ItSt) : ItSt + (ItSt + ItSt) :=
    match it_step X st with
    | ItCont st' => inl st'
    | ItBreak st' => inr (inl st')
    | ItFail st' => inr (inr st')
    end.

  Lemma it_loop_unfold : forall st, it_loop X codes st = iterZ (codes + 1) loopF (fun st => inl st) st.
  Proof. reflexivity. Qed.

  Lemma loop_gen : forall k st fuel tbl0 work0, 0 <= k < NZ -> StM k st ->
    t_tbl st = applyw (trips_writes wl ll root ty table k) tbl0 -> t_work st = work0 ->
    (forall j, 0 <= j < k -> fails_at wl root ty j = false) -> NZ - k <= fuel ->
    match iterZ fuel loopF (fun st => inl st) st with
    | inl st' => first_fail wl root ty = NZ - 1 /\ t_huff st' = hf NZ /\ t_len st' = len_at (NZ - 1) /\
                 t_drop st' = drop (NZ - 1) /\ t_next st' = table + noff (NZ - 1) /\ t_used st' = used (NZ - 1) /\
                 t_tbl st' = applyw (trips_writes wl ll root ty table NZ) tbl0 /\ t_work st' = work0
    | inr st' => first_fail wl root ty < NZ - 1 /\
                 t_tbl st' = applyw (trips_writes wl ll root ty table (first_fail wl root ty + 1)) tbl0 /\ t_work st' = work0
    end.
  Proof.
    intros k st fuel tbl0 work0 Hk. remember (Z.to_nat (NZ - k)) as n eqn:Hn. revert k st fuel Hk Hn.
    induction n as [|n IH]; intros k st fuel Hk Hn SM Et Ew Hnf Hf; [lia|].
    rewrite iterZ_step by lia. unfold loopF at 1.
    pose proof (trip_spec k st Hk SM) as TS.
    destruct (it_step X st) as [st'|st'|st'].
    - destruct TS as (Hk1 & Hfa & SM' & Et' & Ew').
      apply (IH (k + 1)); try lia.
      + exact SM'.
      + rewrite Et', Et, <- applyw_app, <- trips_writes_S by lia. reflexivity.
      + rewrite Ew', Ew. reflexivity.
      + intros j Hj. destruct (Z.eq_dec j k) as [->|NE]; [exact Hfa | apply Hnf; lia].
    - destruct TS as (Hk1 & Eh & El & Ed & En & Eu & Et' & Ew').
      assert (FF : first_fail wl root ty = NZ - 1).
      { unfold ItDefs.first_fail. rewrite zsearch_none; [lia|]. intros j Hj. apply Hnf. lia. }
      rewrite FF. replace (NZ - 1) with k by lia.
      repeat split; try assumption.
      + rewrite Et', Et, <- applyw_app, <- Hk1. rewrite trips_writes_S by lia. rewrite trip_writes_nolink; [reflexivity|].
        unfold ItDefs.link_writes. rewrite <- Hk1. rewrite Z.ltb_irrefl. reflexivity.
      + rewrite Ew', Ew. reflexivity.
    - destruct TS as (Hk1 & Hfa & Et' & Ew').
      assert (FF : first_fail wl root ty = k).
      { unfold ItDefs.first_fail. apply zsearch_eq; [lia | exact Hfa | intros j Hj; apply Hnf; lia]. }
      rewrite FF. split; [lia|]. split.
      + rewrite Et', Et, <- applyw_app. rewrite trips_writes_S by lia. rewrite trip_writes_nolink; [reflexivity|].
        unfold ItDefs.fails_at in Hfa. unfold ItDefs.link_writes.
        destruct ((k + 1 <? NZ) && newtable (k + 1)); [|reflexivity]. cbn [andb] in Hfa |- *. rewrite Hfa. reflexivity.
      + rewrite Ew', Ew. reflexivity.
  Qed.
End Trip.


Section Top.
  Variable ty : codetype.
Variable lens : arr.
Variable lens_ofs : Z.
Variable codes : Z.
Variable ll : list Z.
Variable wl : list Z.
Variable table : Z.
Variable bits : Z.
  Hypothesis Hcodes : 0 <= codes <= 288.
  Hypothesis Hlens : forall i, lens_ofs <= i < lens_ofs + codes -> 0 <= arr_get lens i <= 15.
  Hypothesis Ell : ll = lens_list lens lens_ofs codes.
  Hypothesis Ewl : wl = wl_of ll.
  Hypothesis Hty : ty = CODES -> codes <= 19.
  Hypothesis Hbits : 1 <= bits <= 15.
  #[local] Set Default Proof Using "Hcodes Hlens Ell Ewl Hty Hbits".

  Let HW := HW lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl.
  Let HL := HL lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl.
  Let Hll' := ItSimPre.Hll lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl.

  Lemma ROOT_range : 1 <= MAXL wl -> MINL wl <= ROOT wl bits <= MAXL wl.
  Proof. intros HM. pose proof (MINL_spec wl HW HL HM). unfold ROOT. lia. Qed.

  Theorem inflate_table_abs : forall tbl work, codes <= arr_len work ->
    inflate_table ty lens lens_ofs codes tbl table bits work =
    (let '(ret, ws, toff, bits', ww) := it_abs wl ll ty table bits in
     (ret, applyw ws tbl, toff, bits', applyw ww work)).
  Proof.
    intros tbl work Hwork.
    pose proof (count_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) as [CL CC].
    set (C := CNT lens lens_ofs codes) in CL, CC.
    pose proof (MAXL_spec wl HW HL) as [M1 [M2 M3]].
    unfold inflate_table. change (it_count lens lens_ofs codes (it_zero_count (arr_make 16 0))) with C.
    cbv zeta. rewrite (find_max_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl C CC).
    unfold it_abs.
    destruct (Z.eqb_spec (MAXL wl) 0) as [HM0|HM0]; [reflexivity|].
    assert (HM1 : 1 <= MAXL wl) by lia.
    rewrite (find_min_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl C CC HM1).
    rewrite (left_check_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl C CC).
    pose proof (LEFT_sign wl HW HL) as [LS1 [LS2 LS3]].
    destruct (Z.ltb_spec (LEFT wl) 0) as [HL0|HL0]; [reflexivity|].
    assert (HK : TM wl (MAXL wl) <= 2 ^ MAXL wl) by lia.
    destruct ((0 <? LEFT wl) && (codetype_eqb ty CODES || negb (MAXL wl =? 1))) eqn:Hinc; [reflexivity|].
    pose proof (offs_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl C CC) as [OL OC].
    change (it_offs C (arr_make 16 0)) with (OFS C).
    set (O := OFS C) in OL, OC |- *.
    pose proof (sort_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl O work OL OC) as SS.
    match goal with |- context [it_sort ?a ?b ?c ?d] => set (SRT := it_sort a b c d) in * end.
    clearbody SRT. destruct SRT as [O' work']. cbn [snd] in SS. subst work'.
    assert (ER : (if (if MAXL wl <? bits then MAXL wl else bits) <? MINL wl then MINL wl
                  else if MAXL wl <? bits then MAXL wl else bits) = ROOT wl bits).
    { unfold ROOT. destruct (Z.ltb_spec (MAXL wl) bits); [destruct (Z.ltb_spec (MAXL wl) (MINL wl))|destruct (Z.ltb_spec bits (MINL wl))]; lia. }
    rewrite ER. pose proof (ROOT_range HM1) as RR. set (root := ROOT wl bits) in *.
    pose proof (root_range wl HW HL root RR HM1) as RR2.
    rewrite shl32_pow2 by lia.
    destruct (it_not_enough ty (2 ^ root)) eqn:NE0; [reflexivity|].
    change (mkItCtx ty lens lens_ofs table root (MAXL wl) (2 ^ root - 1)) with (X ty lens lens_ofs wl table root).
    rewrite (it_loop_unfold ty lens lens_ofs codes ll wl table root Hcodes Hlens Ell Ewl RR HM1 HK Hty).
    pose proof (NZ_pos wl HW HL HM1) as NP. pose proof (NZ_le_codes lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) as NC0.
    pose proof (loop_gen ty lens lens_ofs codes ll wl table root Hcodes Hlens Ell Ewl RR HM1 HK Hty
                  0 (mkItSt 0 0 (MINL wl) table root 0 4294967295 (2 ^ root) 0 C tbl (applyw (sort_writes wl ll) work))
                  (codes + 1) tbl (applyw (sort_writes wl ll) work) ltac:(lia)) as LG.
    unfold loop_abs.
    match type of LG with ?P -> _ => assert (SM0 : P) end.
    { unfold StM. cbn [t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_count t_work].
      pose proof (lay_inv wl HW HL root RR HM1 0 ltac:(lia)) as [LI _].
      assert (HS : islong wl root 0 = false).
      { unfold islong. rewrite (len_at_0 wl HW HL HM1). apply Z.ltb_ge. lia. }
      destruct (LI HS) as [N0 [C0 U0]]. rewrite N0, C0, U0. unfold ItDefs.drop, ItDefs.low. rewrite HS.
      rewrite (len_at_0 wl HW HL HM1).
      repeat split; try reflexivity; try lia.
      - intros l Hl. rewrite CC by lia. unfold REM. rewrite (len_at_0 wl HW HL HM1).
        pose proof (MINL_spec wl HW HL HM1) as [A [B D]]. unfold rank_at. rewrite (len_at_0 wl HW HL HM1).
        rewrite (OFF_below_MINL wl HW HL (MINL wl)) by lia.
        destruct (Z.ltb_spec l (MINL wl)); [apply D; lia|]. destruct (Z.eqb_spec l (MINL wl)); [subst; lia | reflexivity].
      - intros j Hj. rewrite Ewl in Hj |- *. apply (sorted_work ll Hll'); [|exact Hj].
        pose proof (NZ_le_NC ll Hll') as NN. rewrite (NC_ll lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) in NN. lia. }
    specialize (LG SM0 eq_refl eq_refl ltac:(intros; lia) ltac:(lia)).
    cbn [t_tbl t_work] in LG.
    destruct (iterZ (codes + 1) (loopF ty lens lens_ofs wl table root) (fun st => inl st) _) as [st|st].
    - destruct LG as (FF & Eh & El & Ed & En & Eu & Et & Ew).
      rewrite FF. rewrite Z.ltb_irrefl. rewrite Eh, El, Ed, En, Eu, Et, Ew.
      unfold final_writes. destruct (Z.eqb_spec (hf wl (NZ wl)) 0) as [Z0|Z0]; cbn [negb].
      + rewrite app_nil_r. reflexivity.
      + rewrite applyw_snoc. reflexivity.
    - destruct LG as (FF & Et & Ew). destruct (Z.ltb_spec (first_fail wl root ty) (NZ wl - 1)); [|lia].
      rewrite Et, Ew. reflexivity.
  Qed.
End Top.
End ItSim2.

Module ItCover.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItMath.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItSort.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma fillset : forall c l y s, 0 <= l <= c -> 0 <= y < 2 ^ c -> 0 <= s < 2 ^ l ->
  (y mod 2 ^ l = rev l s <-> rev c y / 2 ^ (c - l) = s).
Proof.
  intros c l y s Hl Hy Hs.
  assert (E0 : rev c y = rev (l + (c - l)) y) by (f_equal; lia). rewrite E0. rewrite rev_split by lia.
  pose proof (rev_bound (c - l) (y / 2 ^ l) ltac:(lia)) as B.
  rewrite Z.div_add_l by (apply Z.pow_nonzero; lia). rewrite (Z.div_small _ _ B). rewrite Z.add_0_r.
  pose proof (Z.mod_pos_bound y (2 ^ l) ltac:(apply pow2_pos; lia)) as M.
  split.
  - intros E. rewrite E. apply rev_rev; lia.
  - intros E. apply (rev_inj l); try lia; [apply rev_bound; lia|]. rewrite rev_rev by lia. exact E.
Qed.

Lemma in_progression : forall base l e x, 0 <= l -> 0 <= e -> 0 <= base < 2 ^ l ->
  0 <= x < 2 ^ (l + e) -> x mod 2 ^ l = base ->
  exists j, 0 <= j < 2 ^ e /\ x = base + j * 2 ^ l.
Proof.
  intros base l e x Hl He Hb Hx Hm. exists (x / 2 ^ l).
  pose proof (pow2_pos l Hl). pose proof (Z.div_mod x (2 ^ l) ltac:(lia)).
  rewrite Z.pow_add_r in Hx by lia.
  split; [|lia]. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. lia.
Qed.


Section Cover.
  Variable wl : list Z.
Variable ll : list Z.
Variable root : Z.
Variable ty : codetype.
Variable table : Z.
  Hypothesis HW : forall l, 0 <= W wl l.
  Hypothesis HL : length wl = 16%nat.
  Hypothesis Hroot : MINL wl <= root <= MAXL wl.
  Hypothesis HM1 : 1 <= MAXL wl.
  Hypothesis HK : TM wl (MAXL wl) <= 2 ^ MAXL wl.
  #[local] Set Default Proof Using "HW HL Hroot HM1 HK".

  Local Notation W := (W wl).
  Local Notation NZ := (NZ wl).
  Local Notation MAXL := (MAXL wl).
  Local Notation TM := (TM wl).
  Local Notation len_at := (len_at wl).
  Local Notation rank_at := (rank_at wl).
  Local Notation Apos := (Apos wl).
  Local Notation Anext := (Anext wl).
  Local Notation code := (code wl).
  Local Notation hf := (hf wl).
  Local Notation GR := (GR wl root).
  Local Notation Pfx := (Pfx wl root).
  Local Notation islong := (islong wl root).
  Local Notation newtable := (newtable wl root).
  Local Notation noff := (noff wl root).
  Local Notation curr := (curr wl root).
  Local Notation used := (used wl root).
  Local Notation drop := (drop wl root).
  Local Notation wsym := (wsym wl ll).
  Local Notation fill_writes := (fill_writes wl ll root ty table).
  Local Notation link_writes := (link_writes wl root ty table).
  Local Notation trip_writes := (trip_writes wl ll root ty table).
  Local Notation trips_writes := (trips_writes wl ll root ty table).

  Lemma In_fill_writes : forall k i v, 0 <= len_at k - drop k <= curr k ->
    In (i, v) (fill_writes k) <->
    v = here wl ll root ty k /\
    exists j, 0 <= j < 2 ^ (curr k - (len_at k - drop k)) /\
              i = table + noff k + hf k / 2 ^ drop k + j * 2 ^ (len_at k - drop k).
  Proof.
    intros k i v Hk. unfold ItDefs.fill_writes. rewrite in_map_iff. split.
    - intros [j [E Hj]]. apply in_rev, in_seq in Hj. injection E; intros <- <-. split; [reflexivity|].
      exists (Z.of_nat j). split; [|reflexivity]. pose proof (Z.pow_nonneg 2 (curr k - (len_at k - drop k))). lia.
    - intros [-> [j [Hj ->]]]. exists (Z.to_nat j). split; [rewrite Z2Nat.id by lia; reflexivity|].
      apply (proj1 (in_rev (seq _ _) _)). apply in_seq. lia.
  Qed.

  Lemma In_link_writes : forall k i v,
    In (i, v) (link_writes k) <->
    k + 1 < NZ /\ newtable (k + 1) = true /\ it_not_enough ty (used (k + 1)) = false /\
    i = table + rev root (Pfx (k + 1)) /\ v = code_pack (curr (k + 1)) root (noff (k + 1)).
  Proof.
    intros k i v. unfold ItDefs.link_writes.
    destruct (Z.ltb_spec (k + 1) NZ) as [LT|GE]; destruct (newtable (k + 1)); destruct (it_not_enough ty (used (k + 1)));
      cbn [andb negb]; split.
    all: first [ solve [intros [HH|[]]; injection HH; intros <- <-; repeat split; try reflexivity; lia]
               | solve [intros (H1 & H2 & H3 & -> & ->); first [discriminate H2 | discriminate H3 | lia | (left; reflexivity)]]
               | solve [intros []] ].
  Qed.

  Lemma In_trips_writes : forall n p, 0 <= n ->
    In p (trips_writes n) <-> exists k, 0 <= k < n /\ In p (trip_writes k).
  Proof.
    intros n p Hn. unfold ItDefs.trips_writes. rewrite in_flat_map. split.
    - intros [j [Hj Hp]]. apply in_seq in Hj. exists (Z.of_nat j). split; [lia|exact Hp].
    - intros [k [Hk Hp]]. exists (Z.to_nat k). split; [apply in_seq; lia|]. rewrite Z2Nat.id by lia. exact Hp.
  Qed.

  Lemma In_trip_writes : forall k p,
    In p (trip_writes k) <-> In p (fill_writes k) \/ In p (link_writes k).
  Proof. intros k p. unfold ItDefs.trip_writes. apply in_app_iff. Qed.


  Lemma newtable_unique : forall g g', 0 <= g < NZ -> 0 <= g' < NZ ->
    newtable g = true -> newtable g' = true -> Pfx g = Pfx g' -> g = g'.
  Proof.
    intros g g' Hg Hg' N N' E.
    assert (GEN : forall a b, 0 <= a < b -> b < NZ -> newtable a = true -> newtable b = true -> Pfx a = Pfx b -> False).
    { intros a b Hab Hb Na Nb Eab.
      pose proof (newtable_long wl HW HL root Hroot HM1 a Na) as La.
      pose proof (islong_mono wl HW HL root Hroot HM1 a (b - 1) ltac:(lia) ltac:(lia) La) as Lb1.
      pose proof (Pfx_mono wl HW HL root Hroot HM1 a (b - 1) ltac:(lia) ltac:(lia)) as M1.
      pose proof (Pfx_mono wl HW HL root Hroot HM1 (b - 1) b ltac:(lia) ltac:(lia)) as M2.
      unfold ItDefs.newtable in Nb. rewrite Lb1 in Nb. apply Bool.andb_true_iff in Nb as [_ Nb]. cbn [negb orb] in Nb.
      destruct (Z.eqb_spec (Pfx b) (Pfx (b - 1))); [discriminate Nb | lia]. }
    destruct (Z.lt_total g g') as [LT|[EQ|GT]]; [exfalso; apply (GEN g g'); auto; lia | exact EQ | exfalso; apply (GEN g' g); auto; lia].
  Qed.

  Lemma subtable_of : forall k x, 0 <= k < NZ -> 2 ^ root <= x < used k ->
    exists g, 0 <= g <= k /\ newtable g = true /\ noff g <= x < noff g + 2 ^ curr g.
  Proof.
    intros k x Hk. remember (Z.to_nat k) as n eqn:Hn. revert k Hk Hn.
    induction n as [|n IH]; intros k Hk Hn Hx.
    - exfalso. replace k with 0 in Hx by lia. unfold ItDefs.used in Hx. rewrite (lay_0 wl HW HL root Hroot HM1) in Hx. cbn [snd] in Hx. lia.
    - destruct (newtable k) eqn:N.
      + pose proof (lay_S_new wl HW HL root Hroot HM1 (k - 1) ltac:(lia)) as LS. replace (k - 1 + 1) with k in LS by lia.
        destruct (LS N) as [En [Ec Eu]].
        pose proof (used_eq wl HW HL root Hroot HM1 (k - 1) ltac:(lia)) as UE.
        destruct (Z.lt_ge_cases x (used (k - 1))) as [LT|GE].
        * destruct (IH (k - 1) ltac:(lia) ltac:(lia) ltac:(lia)) as [g [G1 [G2 G3]]]. exists g. repeat split; try lia; assumption.
        * exists k. rewrite En. repeat split; try lia; try assumption.
      + pose proof (lay_S_same wl HW HL root Hroot HM1 (k - 1) ltac:(lia)) as LS. replace (k - 1 + 1) with k in LS by lia.
        assert (Eu : used k = used (k - 1)) by (unfold ItDefs.used; rewrite (LS N); reflexivity).
        destruct (IH (k - 1) ltac:(lia) ltac:(lia) ltac:(rewrite <- Eu; exact Hx)) as [g [G1 [G2 G3]]].
        exists g. repeat split; try lia; assumption.
  Qed.

  Lemma used_enough : it_not_enough ty (2 ^ root) = false ->
    (forall k, 0 <= k < NZ - 1 -> fails_at wl root ty k = false) ->
    forall k, 0 <= k < NZ -> it_not_enough ty (used k) = false.
  Proof.
    intros H0 Hnf k Hk. remember (Z.to_nat k) as n eqn:Hn. revert k Hk Hn.
    induction n as [|n IH]; intros k Hk Hn.
    - replace k with 0 by lia. unfold ItDefs.used. rewrite (lay_0 wl HW HL root Hroot HM1). cbn [snd]. exact H0.
    - destruct (newtable k) eqn:N.
      + specialize (Hnf (k - 1) ltac:(lia)). unfold ItDefs.fails_at in Hnf.
        replace (k - 1 + 1) with k in Hnf by lia. rewrite N in Hnf.
        destruct (Z.ltb_spec k NZ); [|lia]. cbn [andb] in Hnf. exact Hnf.
      + pose proof (lay_S_same wl HW HL root Hroot HM1 (k - 1) ltac:(lia)) as LS. replace (k - 1 + 1) with k in LS by lia.
        unfold ItDefs.used. rewrite (LS N). apply (IH (k - 1)); lia.
  Qed.


  Lemma hf_div_bound : forall k, 0 <= k < NZ -> 0 <= hf k / 2 ^ drop k < 2 ^ (len_at k - drop k).
  Proof.
    intros k Hk. rewrite (hf_spec wl HW HL HK k Hk).
    pose proof (curr_range wl HW HL root Hroot HM1 k Hk) as [C1 [C2 C3]].
    pose proof (len_at_spec wl HW HL k Hk) as [L _]. pose proof (code_nonneg wl HW HL k Hk).
    assert (Hd : 0 <= drop k) by (unfold ItDefs.drop; pose proof (root_range wl HW HL root Hroot HM1); destruct (islong k); lia).
    rewrite rev_div by lia. apply rev_bound. lia.
  Qed.

  Lemma fill_writes_range : forall k i v, 0 <= k < NZ -> In (i, v) (fill_writes k) ->
    table + noff k <= i < table + noff k + 2 ^ curr k.
  Proof.
    intros k i v Hk Hin. pose proof (curr_range wl HW HL root Hroot HM1 k Hk) as [C1 [C2 C3]].
    apply (In_fill_writes k i v ltac:(lia)) in Hin as [_ [j [Hj ->]]].
    pose proof (hf_div_bound k Hk) as HB.
    set (l := len_at k - drop k) in *. set (e := curr k - l) in *.
    replace (curr k) with (l + e) by lia. rewrite Z.pow_add_r by lia.
    pose proof (pow2_pos l ltac:(lia)). pose proof (pow2_pos e ltac:(lia)). nia.
  Qed.

  Lemma used_noff_curr : forall k, 0 <= k < NZ -> noff k + 2 ^ curr k = used k.
  Proof. intros k Hk. symmetry. apply (used_eq wl HW HL root Hroot HM1 k Hk). Qed.

  Lemma trips_writes_range : forall n i v, 0 <= n <= NZ -> In (i, v) (trips_writes n) ->
    table <= i < table + used (NZ - 1).
  Proof.
    intros n i v Hn Hin. apply (In_trips_writes n (i, v) ltac:(lia)) in Hin as [k [Hk Hin]].
    pose proof (root_range wl HW HL root Hroot HM1) as RR.
    pose proof (used_mono wl HW HL root Hroot HM1 k (NZ - 1) ltac:(lia) ltac:(lia)) as UM.
    pose proof (used_lower wl HW HL root Hroot HM1 (NZ - 1) ltac:(lia)) as UL.
    apply In_trip_writes in Hin as [Hin|Hin].
    - pose proof (fill_writes_range k i v ltac:(lia) Hin). pose proof (used_noff_curr k ltac:(lia)).
      pose proof (curr_range wl HW HL root Hroot HM1 k ltac:(lia)) as [_ [_ C3]]. lia.
    - apply In_link_writes in Hin as (Hk1 & N & _ & -> & _).
      pose proof (Pfx_bound wl HW HL root Hroot HM1 HK (k + 1) ltac:(lia)). pose proof (Pfx_nonneg wl HW HL root Hroot HM1 (k + 1) ltac:(lia)).
      pose proof (rev_bound root (Pfx (k + 1)) ltac:(lia)). lia.
  Qed.

  Hypothesis HC : TM MAXL = 2 ^ MAXL.
  Hypothesis Hnf : forall k, 0 <= k < NZ - 1 -> fails_at wl root ty k = false.
  Hypothesis H0 : it_not_enough ty (2 ^ root) = false.
  #[local] Set Default Proof Using "HW HL Hroot HM1 HK HC Hnf H0".

  Lemma cover_root_short : forall x, 0 <= x < 2 ^ root -> rev root x * GR < TM root ->
    exists k v, 0 <= k < NZ /\ In (table + x, v) (fill_writes k).
  Proof.
    intros x Hx Hv. pose proof (root_range wl HW HL root Hroot HM1) as RR. pose proof (GR_pos wl HW HL root Hroot HM1) as GP.
    set (v := rev root x) in *. pose proof (rev_bound root x ltac:(lia)) as VB. fold v in VB.
    assert (Ht : 0 <= v * GR < TM MAXL) by (pose proof (TM_mono wl HW HL root MAXL ltac:(lia)); nia).
    destruct (find_code wl HW HL root Hroot HM1 (v * GR) Ht) as [k [Hk [A1 A2]]].
    pose proof (found_short wl HW HL root Hroot HM1 k Hk ltac:(lia)) as HS.
    pose proof (lay_inv wl HW HL root Hroot HM1 k Hk) as [LI _]. destruct (LI HS) as [En [Ec Eu]].
    assert (Ed : drop k = 0) by (unfold ItDefs.drop; rewrite HS; reflexivity).
    pose proof HS as HS'. unfold ItDefs.islong in HS'. apply Z.ltb_ge in HS'.
    pose proof (len_at_spec wl HW HL k Hk) as [L _]. pose proof (len_at_range wl HW HL k Hk) as LR.
    pose proof (code_nonneg wl HW HL k Hk) as CN. pose proof (code_bound wl HW HL HK k Hk) as CB.
    pose proof (code_mul wl HW HL k Hk) as CM. unfold Anext in A2.
    assert (E2 : 2 ^ (MAXL - len_at k) = 2 ^ (root - len_at k) * GR).
    { unfold ItDefs.GR. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    assert (Hq : v / 2 ^ (root - len_at k) = code k).
    { pose proof (pow2_pos (root - len_at k) ltac:(lia)) as PP.
      assert (code k * 2 ^ (root - len_at k) <= v < (code k + 1) * 2 ^ (root - len_at k)) by nia.
      symmetry. apply Z.div_unique with (r := v - code k * 2 ^ (root - len_at k)); [left; lia | lia]. }
    exists k, (here wl ll root ty k). split; [exact Hk|].
    apply (In_fill_writes k); [rewrite Ed, Ec; lia|]. split; [reflexivity|].
    rewrite Ed, En, Ec. rewrite Z.sub_0_r. change (2 ^ 0) with 1. rewrite Z.div_1_r.
    rewrite (hf_spec wl HW HL HK k Hk).
    destruct (in_progression (rev (len_at k) (code k)) (len_at k) (root - len_at k) x) as [j [Hj Ej]]; try lia.
    - apply rev_bound. lia.
    - replace (len_at k + (root - len_at k)) with root by lia. exact Hx.
    - apply (proj2 (fillset root (len_at k) x (code k) ltac:(lia) Hx ltac:(lia))). exact Hq.
    - exists j. split; [exact Hj|]. lia.
  Qed.

  Lemma cover_root_link : forall x, 0 <= x < 2 ^ root -> TM root <= rev root x * GR ->
    exists k v, 0 <= k < NZ /\ In (table + x, v) (link_writes k).
  Proof.
    intros x Hx Hv. pose proof (root_range wl HW HL root Hroot HM1) as RR. pose proof (GR_pos wl HW HL root Hroot HM1) as GP.
    set (v := rev root x) in *. pose proof (rev_bound root x ltac:(lia)) as VB. fold v in VB.
    assert (HP : TM root / GR <= v < 2 ^ root).
    { split; [|lia]. apply Z.div_le_upper_bound; [lia|]. nia. }
    destruct (prefix_has_group wl HW HL root Hroot HM1 HC v HP) as [g [Hg [N E]]].
    assert (Hg1 : 1 <= g).
    { destruct (Z.eq_dec g 0) as [->|]; [|lia]. exfalso.
      pose proof (newtable_long wl HW HL root Hroot HM1 0 N) as L0. unfold ItDefs.islong in L0.
      rewrite (len_at_0 wl HW HL HM1) in L0. apply Z.ltb_lt in L0. lia. }
    exists (g - 1), (code_pack (curr g) root (noff g)). split; [lia|].
    apply In_link_writes. replace (g - 1 + 1) with g by lia.
    split; [lia|]. split; [exact N|]. split; [apply used_enough; [exact H0 | exact Hnf | lia]|].
    split; [|reflexivity]. rewrite E. subst v. rewrite rev_rev by lia. reflexivity.
  Qed.

  Lemma cover_sub : forall x, 2 ^ root <= x < used (NZ - 1) ->
    exists k v, 0 <= k < NZ /\ In (table + x, v) (fill_writes k).
  Proof.
    intros x Hx. pose proof (root_range wl HW HL root Hroot HM1) as RR. pose proof (GR_pos wl HW HL root Hroot HM1) as GP.
    pose proof (NZ_pos wl HW HL HM1) as NP. pose proof (MAXL_spec wl HW HL) as [MM _].
    destruct (subtable_of (NZ - 1) x ltac:(lia) Hx) as [g [Hg [N R]]].
    pose proof (newtable_long wl HW HL root Hroot HM1 g N) as Lg.
    pose proof (lay_inv wl HW HL root Hroot HM1 g ltac:(lia)) as [_ LI]. destruct (LI Lg) as (N1 & N2 & N3 & N4 & N5).
    set (c := curr g) in *. set (y := x - noff g).
    assert (Hy : 0 <= y < 2 ^ c) by (subst y; lia).
    set (u := rev c y). pose proof (rev_bound c y ltac:(lia)) as UB. fold u in UB.
    set (P := Pfx g). set (t := P * GR + u * 2 ^ (MAXL - root - c)).
    assert (Eg : 2 ^ c * 2 ^ (MAXL - root - c) = GR).
    { unfold ItDefs.GR. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    pose proof (group_start wl HW HL root Hroot HM1 g ltac:(lia) N) as GS. fold P in GS.
    assert (HP : TM root / GR <= P < 2 ^ root).
    { split.
      - pose proof (proj1 (islong_iff wl HW HL root Hroot HM1 g ltac:(lia)) Lg) as HK0.
        pose proof (K0_range wl HW HL root Hroot HM1) as KR. unfold K0 in KR.
        pose proof (Apos_K0 wl HW HL root Hroot HM1 ltac:(unfold K0; lia)) as AK. unfold K0 in AK.
        pose proof (Apos_mono wl HW HL (OFF wl (root + 1)) g ltac:(lia) ltac:(lia)) as AM. rewrite AK in AM.
        apply Z.div_le_upper_bound; [lia|]. lia.
      - apply (Pfx_bound wl HW HL root Hroot HM1 HK g ltac:(lia)). }
    assert (Ht : P * GR <= t < (P + 1) * GR).
    { subst t. pose proof (pow2_pos (MAXL - root - c) ltac:(lia)). nia. }
    destruct (in_group wl HW HL root Hroot HM1 HC P t HP Ht) as [j [Hj [Lj [Pj [A1 A2]]]]].
    destruct (group_of wl HW HL root Hroot HM1 j Hj Lj) as [g' [Hg' [N' [P' G4]]]].
    assert (Egg : g' = g) by (apply newtable_unique; try lia; try assumption; rewrite P', Pj; reflexivity).
    subst g'. destruct (G4 j ltac:(lia)) as [Elay [EP _]].
    assert (En : noff j = noff g) by (unfold ItDefs.noff; rewrite Elay; reflexivity).
    assert (Ec : curr j = c) by (unfold c, ItDefs.curr; rewrite Elay; reflexivity).
    assert (Ed : drop j = root) by (unfold ItDefs.drop; rewrite Lj; reflexivity).
    pose proof (lay_inv wl HW HL root Hroot HM1 j Hj) as [_ LJ]. destruct (LJ Lj) as (J1 & J2 & J3 & J4 & J5). rewrite Ec in J2.
    pose proof Lj as Lj'. unfold ItDefs.islong in Lj'. apply Z.ltb_lt in Lj'.
    pose proof (len_at_spec wl HW HL j Hj) as [L _]. pose proof (len_at_range wl HW HL j Hj) as LR.
    set (l := len_at j - root) in *.
    pose proof (Apos_decomp wl HW HL root Hroot HM1 j Hj Lj) as [D1 [D2 D3]]. fold l in D1, D2, D3. rewrite Pj in D1.
    set (sfx := code j mod 2 ^ l) in *. unfold Anext in A2.
    assert (E3 : 2 ^ (MAXL - len_at j) = 2 ^ (c - l) * 2 ^ (MAXL - root - c)).
    { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    assert (Hq : u / 2 ^ (c - l) = sfx).
    { pose proof (pow2_pos (c - l) ltac:(lia)) as PP. pose proof (pow2_pos (MAXL - root - c) ltac:(lia)) as PQ.
      assert (sfx * 2 ^ (c - l) <= u < (sfx + 1) * 2 ^ (c - l)).
      { subst t. rewrite E3 in D1, A2. clear - A1 A2 D1 PP PQ. split; nia. }
      symmetry. apply Z.div_unique with (r := u - sfx * 2 ^ (c - l)); [left; lia | lia]. }
    exists j, (here wl ll root ty j). split; [exact Hj|].
    apply (In_fill_writes j); [rewrite Ed, Ec; lia|]. split; [reflexivity|].
    rewrite Ed, En, Ec. fold l.
    rewrite (hf_spec wl HW HL HK j Hj). pose proof (code_nonneg wl HW HL j Hj) as CN.
    rewrite rev_div by lia. fold l. fold sfx.
    destruct (in_progression (rev l sfx) l (c - l) y) as [m [Hm Em]]; try lia.
    - apply rev_bound. lia.
    - replace (l + (c - l)) with c by lia. exact Hy.
    - apply (proj2 (fillset c l y sfx ltac:(lia) Hy ltac:(lia))). exact Hq.
    - exists m. split; [exact Hm|]. subst y. lia.
  Qed.

  Theorem coverage : forall i, table <= i < table + used (NZ - 1) ->
    In i (map fst (trips_writes NZ)).
  Proof.
    intros i Hi. pose proof (root_range wl HW HL root Hroot HM1) as RR. pose proof (NZ_pos wl HW HL HM1) as NP.
    set (x := i - table). replace i with (table + x) by lia.
    assert (CASES : (exists k v, 0 <= k < NZ /\ In (table + x, v) (fill_writes k)) \/
                    (exists k v, 0 <= k < NZ /\ In (table + x, v) (link_writes k))).
    { destruct (Z.lt_ge_cases x (2 ^ root)) as [LT|GE].
      - destruct (Z.lt_ge_cases (rev root x * GR) (TM root)).
        + left. apply cover_root_short; lia.
        + right. apply cover_root_link; lia.
      - left. apply cover_sub. lia. }
    destruct CASES as [[k [v [Hk Hin]]]|[k [v [Hk Hin]]]];
      (eapply in_map_fst; apply (In_trips_writes NZ); [lia|]; exists k; split; [exact Hk|]; apply In_trip_writes); [left|right]; exact Hin.
  Qed.

  Lemma hf_NZ_complete : hf NZ = 0.
  Proof.
    pose proof (NZ_pos wl HW HL HM1) as NP. rewrite (hf_N wl HW HL) by lia.
    pose proof (Apos_last wl HW HL HM1) as AL. pose proof (code_mul wl HW HL (NZ - 1) ltac:(lia)) as CM.
    rewrite (len_at_last wl HW HL HM1) in *. rewrite Z.sub_diag in *. change (2 ^ 0) with 1 in *.
    destruct (Z.ltb_spec (code (NZ - 1) + 1) (2 ^ MAXL)); [lia|reflexivity].
  Qed.
End Cover.
End ItCover.

Module ItShape.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItMath.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItSort.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItCover.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Lemma nth_bounded : forall (l : list Z) lo hi k, forallb (fun v => (lo <=? v) && (v <? hi)) l = true ->
  lo <= 0 < hi -> lo <= nth k l 0 < hi.
Proof.
  intros l lo hi k H Hz. destruct (Nat.lt_ge_cases k (length l)) as [Hk|Hk].
  - apply (proj1 (forallb_forall _ _)) with (x := nth k l 0) in H; [|apply nth_In; exact Hk].
    apply Bool.andb_true_iff in H as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. lia.
  - rewrite nth_overflow by lia. lia.
Qed.

Lemma lext_byte : forall k, 0 <= nth k lext_l 0 < 256.
Proof. intros k. apply nth_bounded; [vm_compute; reflexivity | lia]. Qed.
Lemma dext_byte : forall k, 0 <= nth k dext_l 0 < 256.
Proof. intros k. apply nth_bounded; [vm_compute; reflexivity | lia]. Qed.
Lemma lbase_short : forall k, 0 <= nth k lbase_l 0 < 65536.
Proof. intros k. apply nth_bounded; [vm_compute; reflexivity | lia]. Qed.
Lemma dbase_short : forall k, 0 <= nth k dbase_l 0 < 65536.
Proof. intros k. apply nth_bounded; [vm_compute; reflexivity | lia]. Qed.

Lemma sym_entry_range : forall ty s, 0 <= s < nsyms ty ->
  0 <= fst (sym_entry ty s) < 256 /\ 0 <= snd (sym_entry ty s) < 65536.
Proof.
  intros ty s Hs. destruct ty; cbn [sym_entry nsyms] in *.
  - cbn. lia.
  - destruct (Z.ltb_spec s 256); [cbn; lia|]. destruct (Z.eqb_spec s 256); [cbn; lia|].
    cbn [fst snd]. pose proof (lext_byte (Z.to_nat (s - 257))). pose proof (lbase_short (Z.to_nat (s - 257))). lia.
  - cbn [fst snd]. pose proof (dext_byte (Z.to_nat s)). pose proof (dbase_short (Z.to_nat s)). lia.
Qed.

Lemma wrap8_idem : forall z, wrap8 (wrap8 z) = wrap8 z.
Proof.
  intros z. apply wrap8_small. unfold wrap8. change 255 with (2 ^ 8 - 1). rewrite land_ones' by lia. apply Z.mod_pos_bound. lia.
Qed.

Lemma entry_sym_entry : forall ty s, 0 <= s ->
  wrap8 (fst (entry ty s)) = fst (sym_entry ty s) /\ snd (entry ty s) = snd (sym_entry ty s).
Proof.
  intros ty s Hs. destruct ty; cbn [entry sym_entry].
  - cbn [fst snd]. rewrite wrap8_small by lia. split; reflexivity.
  - destruct (Z.ltb_spec (s + 1) 257), (Z.ltb_spec s 256); try lia.
    + cbn [fst snd]. rewrite wrap8_small by lia. split; reflexivity.
    + destruct (Z.leb_spec 257 s), (Z.eqb_spec s 256); try lia; cbn [fst snd].
      * rewrite wrap8_idem. rewrite wrap8_small by apply lext_byte. split; reflexivity.
      * rewrite wrap8_small by lia. split; reflexivity.
  - cbn [fst snd]. rewrite wrap8_idem. rewrite wrap8_small by apply dext_byte. split; reflexivity.
Qed.


Section Shape.
  Variable wl : list Z.
Variable ll : list Z.
Variable root : Z.
Variable ty : codetype.
Variable table : Z.
  Hypothesis Hll : Forall (fun l => 0 <= l <= 15) ll.
  Hypothesis Ewl : wl = wl_of ll.
  Hypothesis Hroot : MINL wl <= root <= MAXL wl.
  Hypothesis HM1 : 1 <= MAXL wl.
  Hypothesis HK : TM wl (MAXL wl) <= 2 ^ MAXL wl.
  Hypothesis Hns : NC ll <= nsyms ty.
  Hypothesis HU : used wl root (NZ wl - 1) < 65536.
  #[local] Set Default Proof Using "Hll Ewl Hroot HM1 HK Hns HU".

  Lemma HW' : forall l, 0 <= W wl l.
  Proof. rewrite Ewl. apply (W_of_nonneg ll Hll). Qed.
  Lemma HL' : length wl = 16%nat.
  Proof. rewrite Ewl. apply (wl_of_length ll Hll). Qed.
  Let HW := HW'.
  Let HL := HL'.

  Local Notation NZ := (NZ wl).
  Local Notation MAXL := (MAXL wl).
  Local Notation len_at := (len_at wl).
  Local Notation used := (used wl root).
  Local Notation noff := (noff wl root).
  Local Notation curr := (curr wl root).
  Local Notation drop := (drop wl root).
  Local Notation islong := (islong wl root).
  Local Notation newtable := (newtable wl root).
  Local Notation wsym := (wsym wl ll).

  Lemma wsym_ok : forall k, 0 <= k < NZ -> 0 <= wsym k < nsyms ty /\ LofS ll (wsym k) = len_at k.
  Proof.
    intros k Hk. pose proof (wsym_spec ll Hll k) as WS. rewrite <- Ewl in WS. specialize (WS Hk). destruct WS as [A B].
    split; [lia | exact B].
  Qed.

  Lemma here_shape : forall k x, 0 <= k < NZ ->
    (islong k = false -> x < 2 ^ root) -> (islong k = true -> 2 ^ root <= x) ->
    entry_shape ty root (used (NZ - 1)) x (here wl ll root ty k).
  Proof.
    intros k x Hk Hs Hlg. pose proof (root_range wl HW HL root Hroot HM1) as RR.
    pose proof (wsym_ok k Hk) as [SR SL]. pose proof (len_at_spec wl HW HL k Hk) as [L _].
    unfold here. destruct (entry ty (wsym k)) as [op val] eqn:E.
    pose proof (entry_sym_entry ty (wsym k) ltac:(lia)) as [E1 E2]. rewrite E in E1, E2. cbn [fst snd] in E1, E2.
    pose proof (sym_entry_range ty (wsym k) SR) as [B1 B2].
    left. exists (wsym k), (len_at k). split; [exact SR|]. split; [exact L|].
    rewrite code_op_pack, code_val_pack, code_bits_pack. rewrite E1. split; [reflexivity|].
    rewrite <- E2. split; [apply wrap16_small; rewrite E2; lia|].
    unfold ItDefs.drop. destruct (islong k) eqn:HLg.
    - right. pose proof HLg as H'. unfold ItDefs.islong in H'. apply Z.ltb_lt in H'.
      rewrite wrap8_small by lia. specialize (Hlg eq_refl). repeat split; lia.
    - left. pose proof HLg as H'. unfold ItDefs.islong in H'. apply Z.ltb_ge in H'.
      rewrite Z.sub_0_r, wrap8_small by lia. specialize (Hs eq_refl). repeat split; lia.
  Qed.

  Lemma fill_shape : forall k i v, 0 <= k < NZ -> In (i, v) (fill_writes wl ll root ty table k) ->
    entry_shape ty root (used (NZ - 1)) (i - table) v.
  Proof.
    intros k i v Hk Hin. pose proof (fill_writes_range wl ll root ty table HW HL Hroot HM1 HK k i v Hk Hin) as R.
    pose proof (curr_range wl HW HL root Hroot HM1 k Hk) as [C1 [C2 C3]].
    apply (In_fill_writes wl ll root ty table HW HL Hroot HM1 HK k i v ltac:(lia)) in Hin as [-> _].
    pose proof (lay_inv wl HW HL root Hroot HM1 k Hk) as [LS LL].
    apply here_shape; [exact Hk| |].
    - intros HS. destruct (LS HS) as [En [Ec Eu]]. rewrite En, Ec in R. lia.
    - intros HLg. destruct (LL HLg) as [N1 _]. lia.
  Qed.

  Lemma link_shape : forall k i v, 0 <= k < NZ -> In (i, v) (link_writes wl root ty table k) ->
    entry_shape ty root (used (NZ - 1)) (i - table) v.
  Proof.
    intros k i v Hk Hin. pose proof (root_range wl HW HL root Hroot HM1) as RR. pose proof (MAXL_spec wl HW HL) as [MM _].
    apply (In_link_writes wl root ty table HW HL Hroot HM1 HK) in Hin as (Hk1 & N & _ & -> & ->).
    pose proof (newtable_long wl HW HL root Hroot HM1 (k + 1) N) as Lg.
    pose proof (lay_inv wl HW HL root Hroot HM1 (k + 1) ltac:(lia)) as [_ LL]. destruct (LL Lg) as (N1 & N2 & N3 & N4 & N5).
    pose proof (used_mono wl HW HL root Hroot HM1 (k + 1) (NZ - 1) ltac:(lia) ltac:(lia)) as UM.
    pose proof (Pfx_bound wl HW HL root Hroot HM1 HK (k + 1) ltac:(lia)). pose proof (Pfx_nonneg wl HW HL root Hroot HM1 (k + 1) ltac:(lia)).
    pose proof (rev_bound root (Pfx wl root (k + 1)) ltac:(lia)) as RB.
    pose proof (pow2_le_15 (curr (k + 1)) ltac:(lia)).
    right; left. rewrite code_op_pack, code_val_pack, code_bits_pack.
    rewrite !wrap8_small by lia. rewrite wrap16_small by lia. repeat split; lia.
  Qed.

  Lemma trips_shape : forall i v, In (i, v) (trips_writes wl ll root ty table NZ) ->
    entry_shape ty root (used (NZ - 1)) (i - table) v.
  Proof.
    intros i v Hin. pose proof (NZ_pos wl HW HL HM1).
    apply (In_trips_writes wl ll root ty table HW HL Hroot HM1 HK NZ (i, v) ltac:(lia)) in Hin as [k [Hk Hin]].
    apply (In_trip_writes wl ll root ty table HW HL Hroot HM1 HK) in Hin as [Hin|Hin]; [eapply fill_shape | eapply link_shape]; eauto.
  Qed.
End Shape.
End ItShape.

Module ItTable.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItMath.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItSort.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItCover.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItShape.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition ty_ok (ty : codetype) (ll : list Z) (bits : Z) : Prop :=
  match ty with
  | CODES => NC ll <= 19 /\ 7 <= bits /\ Forall (fun l => l <= 7) ll
  | LENS => NC ll <= 288
  | DISTS => NC ll <= 32
  end.

Section AbsProps.
  Variable wl : list Z.
Variable ll : list Z.
Variable table : Z.
Variable bits : Z.
  Hypothesis Hll : Forall (fun l => 0 <= l <= 15) ll.
  Hypothesis Ewl : wl = wl_of ll.
  Hypothesis Hbits : 1 <= bits <= 15.
  #[local] Set Default Proof Using "Hll Ewl Hbits".

  Lemma HWa : forall l, 0 <= W wl l.
  Proof. rewrite Ewl. apply (W_of_nonneg ll Hll). Qed.
  Lemma HLa : length wl = 16%nat.
  Proof. rewrite Ewl. apply (wl_of_length ll Hll). Qed.
  Let HW := HWa.
  Let HL := HLa.

  Local Notation W := (W wl).
  Local Notation NZ := (NZ wl).
  Local Notation MAXL := (MAXL wl).
  Local Notation MINL := (MINL wl).
  Local Notation TM := (TM wl).
  Local Notation LEFT := (LEFT wl).

  Lemma nsyms_ok : forall ty, ty_ok ty ll bits -> NC ll <= nsyms ty.
  Proof. intros ty Hty. destruct ty; cbn [nsyms]; cbn [ty_ok] in Hty; lia. Qed.

  Lemma room_enough : forall ty u, it_not_enough ty u = false -> ty <> CODES -> u <= it_room ty.
  Proof.
    intros ty u H Hn. destruct ty; cbn [it_not_enough it_room] in *; [congruence| |]; apply Z.ltb_ge in H; exact H.
  Qed.

  Lemma countz_zero : forall x l, Forall (fun v => v <> x) l -> countz x l = 0.
  Proof.
    intros x l H. induction l as [|a l IH]; [reflexivity|].
    apply Forall_cons_iff in H as [Ha Hl]. rewrite countz_cons, (IH Hl).
    destruct (Z.eqb_spec x a); [congruence | reflexivity].
  Qed.

  Lemma codes_short : ty_ok CODES ll bits -> 1 <= MAXL -> ROOT wl bits = MAXL /\ MAXL <= 7.
  Proof.
    intros Hty HM. destruct Hty as [_ [Hb H7]].
    pose proof (MAXL_spec wl HW HL) as [M1 [M2 M3]]. pose proof (MINL_spec wl HW HL HM) as [A _].
    assert (HM7 : MAXL <= 7).
    { destruct (Z.le_gt_cases MAXL 7) as [X|X]; [exact X|]. exfalso.
      specialize (M3 HM). replace (W MAXL) with (ItDefs.W (wl_of ll) MAXL) in M3 by (rewrite <- Ewl; reflexivity).
      rewrite (W_of ll Hll) in M3 by lia.
      rewrite countz_zero in M3; [lia|]. apply Forall_impl with (P := fun l => l <= 7); [intros v Hv; lia | exact H7]. }
    split; [|exact HM7]. unfold ROOT. lia.
  Qed.

  Lemma incomplete_facts : 0 < LEFT -> MAXL = 1 ->
    MINL = 1 /\ W 1 = 1 /\ NZ = 1 /\ ROOT wl bits = 1 /\ TM MAXL <= 2 ^ MAXL.
  Proof.
    intros HLp HM. pose proof (MAXL_spec wl HW HL) as [M1 [M2 M3]]. pose proof (MINL_spec wl HW HL ltac:(lia)) as [A [B C]].
    pose proof (LEFT_sign wl HW HL) as [_ [_ LS]]. apply (proj1 LS) in HLp.
    pose proof (TM_step' wl HW HL 1 ltac:(lia)) as T1. replace (1 - 1) with 0 in T1 by lia. rewrite (TM_0 wl HW HL) in T1.
    pose proof (OFF_MAXL wl HW HL ltac:(lia)) as OM.
    rewrite HM in HLp, T1, A, OM. rewrite (OFF_1 wl HW HL) in OM.
    replace (2 ^ (1 - 1)) with 1 in T1 by reflexivity. change (2 ^ 1) with 2 in HLp.
    assert (E1 : MINL = 1) by lia. rewrite E1 in B.
    assert (W1 : W 1 = 1) by lia.
    repeat split; try lia; unfold ROOT; rewrite ?HM, ?E1; try lia.
    all: match goal with |- ?g => idtac "REMAIN" g end.
  Qed.

  Local Notation len_at := (len_at wl).
  Local Notation hf := (hf wl).

  Lemma first_fail_eq : forall root ty,
    first_fail wl root ty = zsearch (fails_at wl root ty) 0 (Z.to_nat (NZ - 1)).
  Proof. intros root ty. exact (@eq_refl Z (zsearch (fails_at wl root ty) 0 (Z.to_nat (NZ - 1)))). Qed.

  Theorem it_abs_props : forall ty, ty_ok ty ll bits ->
    let '(ret, ws, toff, bits', ww) := it_abs wl ll ty table bits in
    ret = 0 ->
    1 <= bits' <= 15 /\ table + 2 ^ bits' <= toff <= table + it_room ty /\
    (forall i v, In (i, v) ws -> table <= i < toff) /\
    (forall i, table <= i < toff -> In i (map fst ws)) /\
    (forall i v, In (i, v) ws -> entry_shape ty bits' (toff - table) (i - table) v).
  Proof.
    intros ty Hty. pose proof (MAXL_spec wl HW HL) as [M1 [M2 M3]]. pose proof (nsyms_ok ty Hty) as NS.
    assert (HR : 2 <= it_room ty) by (destruct ty; cbn; unfold ENOUGH_LENS, ENOUGH_DISTS; lia).
    unfold it_abs.
    destruct (Z.eqb_spec MAXL 0) as [HM0|HM0].
    {
      intros _. change (2 ^ 1) with 2. split; [lia|]. split; [lia|]. split; [|split].
      - intros i v [H|[H|[]]]; injection H; intros; subst; lia.
      - intros i Hi. cbn [map fst]. assert (i = table \/ i = table + 1) as [->| ->] by lia; [left|right; left]; reflexivity.
      - intros i v Hin. right; right.
        assert (v = code_pack 64 1 0) as -> by (destruct Hin as [H|[H|[]]]; injection H; intros; subst; reflexivity).
        rewrite code_op_pack, code_bits_pack, code_val_pack. cbn. repeat split; reflexivity. }
    assert (HM1 : 1 <= MAXL) by lia.
    pose proof (MINL_spec wl HW HL HM1) as [MA [MB MC]].
    destruct (Z.ltb_spec LEFT 0) as [HL0|HL0]; [intros X; discriminate X|].
    pose proof (LEFT_sign wl HW HL) as [LS1 [LS2 LS3]].
    assert (HK : TM MAXL <= 2 ^ MAXL) by lia.
    destruct ((0 <? LEFT) && (codetype_eqb ty CODES || negb (MAXL =? 1))) eqn:Hinc; [intros X; discriminate X|].
    set (root := ROOT wl bits).
    assert (RR : MINL <= root <= MAXL) by (subst root; unfold ROOT; lia).
    pose proof (root_range wl HW HL root RR HM1) as RR2.
    destruct (it_not_enough ty (2 ^ root)) eqn:NE0; [intros X; discriminate X|].
    unfold loop_abs.
    destruct (Z.ltb_spec (first_fail wl root ty) (NZ - 1)) as [FF|FF]; [intros X; discriminate X|].
    intros _.
    pose proof (NZ_pos wl HW HL HM1) as NP.
    assert (Hnf : forall k, 0 <= k < NZ - 1 -> fails_at wl root ty k = false).
    { intros k Hk. rewrite first_fail_eq in FF. apply (zsearch_before (fails_at wl root ty) 0 (Z.to_nat (NZ - 1))). lia. }
    pose proof (used_lower wl HW HL root RR HM1 (NZ - 1) ltac:(lia)) as UL.
    pose proof (used_enough wl root ty HW HL RR HM1 HK NE0 Hnf (NZ - 1) ltac:(lia)) as UE.
    assert (HU : 2 ^ root <= used wl root (NZ - 1) <= it_room ty).
    { split; [exact UL|]. destruct (codetype_eqb ty CODES) eqn:TC.
      - assert (ty = CODES) as -> by (destruct ty; cbn in TC; congruence).
        destruct (codes_short Hty HM1) as [E7 M7]. fold root in E7.
        pose proof (lay_inv wl HW HL root RR HM1 (NZ - 1) ltac:(lia)) as [LI _].
        assert (HS : islong wl root (NZ - 1) = false).
        { unfold islong. apply Z.ltb_ge. rewrite (len_at_last wl HW HL HM1). lia. }
        destruct (LI HS) as [_ [_ ->]]. cbn [it_room]. rewrite E7.
        change 128 with (2 ^ 7). apply Z.pow_le_mono_r; lia.
      - apply room_enough; [exact UE|]. destruct ty; cbn in TC; congruence. }
    assert (HU2 : used wl root (NZ - 1) < 65536).
    { assert (it_room ty <= 852) by (destruct ty; cbn; unfold ENOUGH_LENS, ENOUGH_DISTS; lia). lia. }
    destruct (Z.eq_dec LEFT 0) as [HC0|HC0].
    -
      assert (HC : TM MAXL = 2 ^ MAXL) by (apply (proj1 LS2); exact HC0).
      unfold final_writes. rewrite (hf_NZ_complete wl root ty HW HL RR HM1 HK HC Hnf NE0). cbn [Z.eqb]. rewrite app_nil_r.
      replace (table + used wl root (NZ - 1) - table) with (used wl root (NZ - 1)) by lia.
      split; [lia|]. split; [lia|]. split; [|split].
      + intros i v Hin. eapply (trips_writes_range wl ll root ty table HW HL RR HM1 HK NZ); [lia | exact Hin].
      + intros i Hi. apply (coverage wl ll root ty table HW HL RR HM1 HK HC Hnf NE0). exact Hi.
      + intros i v Hin. apply (trips_shape wl ll root ty table Hll Ewl RR HM1 HK NS HU2). exact Hin.
    -
      assert (HLp : 0 < LEFT) by lia.
      destruct (Z.ltb_spec 0 LEFT); [|lia]. cbn [andb] in Hinc. apply Bool.orb_false_iff in Hinc as [TC HMx].
      apply Bool.negb_false_iff in HMx. apply Z.eqb_eq in HMx.
      destruct (incomplete_facts HLp HMx) as (Emin & W1 & NZ1 & R1 & _). fold root in R1.
      pose proof (here_shape wl ll root ty Hll Ewl RR HM1 HK NS HU2) as HS.
      unfold final_writes. rewrite NZ1 in *. change (1 - 1) with 0 in *.
      pose proof (lay_0 wl HW HL root RR HM1) as L0.
      assert (E0 : noff wl root 0 = 0 /\ curr wl root 0 = root /\ used wl root 0 = 2 ^ root).
      { unfold noff, curr, used. rewrite L0. repeat split; reflexivity. }
      destruct E0 as (En & Ec & Eu).
      pose proof (len_at_0 wl HW HL HM1) as EL. rewrite Emin in EL.
      assert (Ed : drop wl root 0 = 0).
      { unfold drop, islong. rewrite EL, R1. reflexivity. }
      assert (Ehf0 : hf 0 = 0) by reflexivity.
      assert (Ehf1 : hf 1 = 1).
      { unfold ItDefs.hf. cbn [Z.eqb]. change (1 - 1) with 0. rewrite (code_0 wl HW HL HM1), EL. reflexivity. }
      rewrite Ehf1. cbn [Z.eqb]. assert (P2 : 2 ^ root = 2) by (rewrite R1; reflexivity).
      rewrite ?Eu, ?En, ?EL, ?Ed, ?P2 in *.
      assert (ET : trips_writes wl ll root ty table 1 = fill_writes wl ll root ty table 0).
      { unfold trips_writes. change (Z.to_nat 1) with 1%nat. cbn [seq flat_map]. rewrite app_nil_r.
        change (Z.of_nat 0) with 0. unfold trip_writes, link_writes. rewrite NZ1. cbn [Z.add Z.ltb andb]. apply app_nil_r. }
      rewrite ET.
      assert (HF : forall i v, In (i, v) (fill_writes wl ll root ty table 0) <-> i = table /\ v = here wl ll root ty 0).
      { intros i v. rewrite (In_fill_writes wl ll root ty table HW HL RR HM1 HK 0 i v) by (rewrite EL, Ed, Ec, R1; lia).
        rewrite EL, Ed, Ec, En, Ehf0, R1. change (2 ^ (1 - (1 - 0))) with 1. change (2 ^ 0) with 1. change (0 / 1) with 0.
        split.
        - intros [-> [j [Hj ->]]]. split; [lia|reflexivity].
        - intros [-> ->]. split; [reflexivity|]. exists 0. lia. }
      replace (table + 2 - table) with 2 by lia.
      split; [lia|]. split; [lia|]. split; [|split].
      + intros i v Hin. apply in_app_iff in Hin as [Hin|[Hin|[]]].
        * apply HF in Hin as [-> _]. lia.
        * injection Hin; intros; subst. lia.
      + intros i Hi. rewrite map_app. apply in_app_iff.
        assert (i = table \/ i = table + 1) as [->| ->] by lia.
        * left. eapply in_map_fst. apply (proj2 (HF table (here wl ll root ty 0))). split; reflexivity.
        * right. left. cbn. lia.
      + intros i v Hin. apply in_app_iff in Hin as [Hin|[Hin|[]]].
        * apply HF in Hin as [-> ->]. rewrite Z.sub_diag.
          apply HS; [lia| |]; unfold islong; rewrite ?EL, ?R1; cbn; intros; lia.
        * injection Hin; intros; subst. right; right.
          rewrite code_op_pack, code_bits_pack, code_val_pack. cbn. repeat split; try reflexivity. exact R1.
  Qed.
End AbsProps.
End ItTable.

Module ItProof.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItMath.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItSort.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItSimPre.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItSim2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItCover.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItShape.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItTable.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition may_link_op (op : Z) : bool :=
  (Z.land op 240 =? 0) || ((Z.land op 16 =? 0) && (Z.land op 64 =? 0)).

Lemma may_link_code_op : forall e, may_link e = may_link_op (code_op e).
Proof. reflexivity. Qed.

Lemma forallb_seq : forall f n k, forallb f (seq 0 n) = true -> (k < n)%nat -> f k = true.
Proof.
  intros f n k H Hk. apply (proj1 (forallb_forall f (seq 0 n)) H). apply in_seq. lia.
Qed.

Lemma forallb_nth : forall f (l : list Z) k, forallb f l = true -> (k < length l)%nat -> f (nth k l 0) = true.
Proof.
  intros f l k H Hk. apply (proj1 (forallb_forall f l) H). apply nth_In. exact Hk.
Qed.

Lemma lext_nolink : forall k, (k < 31)%nat -> may_link_op (nth k lext_l 0) = false.
Proof.
  intros k Hk. apply Bool.negb_true_iff.
  apply (forallb_nth (fun v => negb (may_link_op v)) lext_l k); [vm_compute; reflexivity | exact Hk].
Qed.

Lemma dext_nolink : forall k, (k < 32)%nat -> may_link_op (nth k dext_l 0) = false /\ nth k dext_l 0 <> 0.
Proof.
  intros k Hk.
  pose proof (forallb_nth (fun v => negb (may_link_op v) && negb (v =? 0)) dext_l k ltac:(vm_compute; reflexivity) Hk) as H.
  cbn beta in H. apply Bool.andb_true_iff in H as [A B]. apply Bool.negb_true_iff in A. apply Bool.negb_true_iff in B.
  apply Z.eqb_neq in B. split; assumption.
Qed.

Lemma lens_values_ok : forall k, (k < 31)%nat ->
  16 <= nth k lext_l 0 < 32 -> nth k lbase_l 0 + Z.shiftl 1 (Z.land (nth k lext_l 0) 15) - 1 <= 258.
Proof.
  intros k Hk Hop.
  pose proof (forallb_seq (fun k => let op := nth k lext_l 0 in
                                   negb ((16 <=? op) && (op <? 32)) || (nth k lbase_l 0 + Z.shiftl 1 (Z.land op 15) - 1 <=? 258))
                          31 k ltac:(vm_compute; reflexivity) Hk) as H.
  cbn beta zeta in H. apply Bool.orb_true_iff in H as [H|H].
  - apply Bool.negb_true_iff in H. apply Bool.andb_false_iff in H as [H|H]; [apply Z.leb_gt in H | apply Z.ltb_ge in H]; lia.
  - apply Z.leb_le in H. exact H.
Qed.

Lemma sym_entry_nolink : forall ty s, 0 <= s < nsyms ty ->
  fst (sym_entry ty s) = 0 \/ may_link_op (fst (sym_entry ty s)) = false.
Proof.
  intros ty s Hs. destruct ty; cbn [sym_entry nsyms] in *.
  - left. reflexivity.
  - destruct (Z.ltb_spec s 256); [left; reflexivity|].
    destruct (Z.eqb_spec s 256); [right; reflexivity|].
    right. cbn [fst]. apply lext_nolink. lia.
  - right. cbn [fst]. apply (proj1 (dext_nolink (Z.to_nat s) ltac:(lia))).
Qed.


Section Runs.
  Variable ty : codetype.
Variable lens1 : arr.
Variable lens2 : arr.
Variable lens_ofs : Z.
Variable codes : Z.
Variable tbl1 : arr.
Variable tbl2 : arr.
Variable table : Z.
Variable bits : Z.
Variable work1 : arr.
Variable work2 : arr.
  Hypothesis HR : it_inputs_related ty lens1 lens2 lens_ofs codes tbl1 tbl2 table bits work1 work2.
  #[local] Set Default Proof Using "HR".

  Definition LL : list Z := lens_list lens1 lens_ofs codes.
  Definition WL : list Z := wl_of LL.

  Lemma HR' :
    arr_len tbl1 = arr_len tbl2 /\ arr_len work1 = arr_len work2 /\
    0 <= codes <= 288 /\ codes <= arr_len work1 /\
    0 <= table /\ table + it_room ty <= arr_len tbl1 /\
    1 <= bits <= 15 /\
    (forall i, lens_ofs <= i < lens_ofs + codes -> arr_get lens1 i = arr_get lens2 i) /\
    (forall i, lens_ofs <= i < lens_ofs + codes -> 0 <= arr_get lens1 i <= 15) /\
    it_ty_ok ty lens1 lens_ofs codes bits.
  Proof. exact HR. Qed.

  Lemma LL2 : LL = lens_list lens2 lens_ofs codes.
  Proof.
    pose proof HR' as (_ & _ & Hc & _ & _ & _ & _ & Hag & _). unfold LL, lens_list.
    apply map_ext_in. intros n Hn. apply in_seq in Hn. apply Hag. lia.
  Qed.

  Lemma Hlens2 : forall i, lens_ofs <= i < lens_ofs + codes -> 0 <= arr_get lens2 i <= 15.
  Proof. pose proof HR' as (_ & _ & _ & _ & _ & _ & _ & Hag & Hrg & _). intros i Hi. rewrite <- Hag by lia. apply Hrg. lia. Qed.

  Lemma Hty1 : ty = CODES -> codes <= 19.
  Proof. pose proof HR' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & T). intros ->. cbn in T. lia. Qed.

  Lemma LL_Forall : Forall (fun l => 0 <= l <= 15) LL.
  Proof. pose proof HR' as (_ & _ & _ & _ & _ & _ & _ & _ & Hrg & _). unfold LL. apply lens_list_Forall. exact Hrg. Qed.

  Lemma LL_ty_ok : ty_ok ty LL bits.
  Proof.
    pose proof HR' as (_ & _ & Hc & _ & _ & _ & _ & _ & _ & T). unfold ty_ok. unfold it_ty_ok in T.
    assert (E : NC LL = codes) by (unfold LL; apply NC_lens; lia).
    destruct ty; rewrite ?E; try lia.
    destruct T as [A [B C]]. split; [lia|]. split; [lia|].
    unfold LL, lens_list. apply Forall_map. apply Forall_forall. intros n Hn. apply in_seq in Hn. apply C. lia.
  Qed.

  Lemma run1 : inflate_table ty lens1 lens_ofs codes tbl1 table bits work1 =
    (let '(ret, ws, toff, bits', ww) := it_abs WL LL ty table bits in (ret, applyw ws tbl1, toff, bits', applyw ww work1)).
  Proof.
    pose proof HR' as (_ & _ & Hc & Hw & _ & _ & Hb & _ & Hrg & _).
    apply (inflate_table_abs ty lens1 lens_ofs codes LL WL table bits Hc Hrg eq_refl eq_refl Hty1 Hb). exact Hw.
  Qed.

  Lemma run2 : inflate_table ty lens2 lens_ofs codes tbl2 table bits work2 =
    (let '(ret, ws, toff, bits', ww) := it_abs WL LL ty table bits in (ret, applyw ws tbl2, toff, bits', applyw ww work2)).
  Proof.
    pose proof HR' as (_ & Hw12 & Hc & Hw & _ & _ & Hb & _ & Hrg & _).
    apply (inflate_table_abs ty lens2 lens_ofs codes LL WL table bits Hc Hlens2 LL2 eq_refl Hty1 Hb). lia.
  Qed.

  Lemma props : let '(ret, ws, toff, bits', ww) := it_abs WL LL ty table bits in
    ret = 0 ->
    1 <= bits' <= 15 /\ table + 2 ^ bits' <= toff <= table + it_room ty /\
    (forall i v, In (i, v) ws -> table <= i < toff) /\
    (forall i, table <= i < toff -> In i (map fst ws)) /\
    (forall i v, In (i, v) ws -> entry_shape ty bits' (toff - table) (i - table) v).
  Proof.
    pose proof HR' as (_ & _ & _ & _ & _ & _ & Hb & _).
    exact (it_abs_props WL LL table bits LL_Forall eq_refl Hb ty LL_ty_ok).
  Qed.
End Runs.


Ltac setup HR :=
  pose proof (run1 _ _ _ _ _ _ _ _ _ _ _ HR) as R1;
  pose proof (run2 _ _ _ _ _ _ _ _ _ _ _ HR) as R2;
  pose proof (props _ _ _ _ _ _ _ _ _ _ _ HR) as PR;
  pose proof (HR' _ _ _ _ _ _ _ _ _ _ _ HR) as (Ht12 & Hw12 & Hc & Hw & Ht0 & Htr & Hb & Hag & Hrg & Hty);
  cbv zeta; rewrite R1; try rewrite R2; clear R1 R2;
  match goal with |- context [it_abs ?a ?b ?c ?d ?e] =>
    destruct (it_abs a b c d e) as [[[[ret ws] toff] bits'] ww] end;
  cbn [fst snd].

Theorem inftrees_shapes_proof : inftrees_shapes.
Proof.
  intros ty lens1 lens2 lens_ofs codes tbl1 tbl2 table bits work1 work2 HR. setup HR.
  intros Hret i Hi. destruct (PR Hret) as (P1 & P2 & P3 & P4 & P5).
  apply (applyw_all (fun i v => entry_shape ty bits' (toff - table) (i - table) v)); [exact P5 | apply P4; exact Hi | lia].
Qed.

Theorem inftrees_coverage_proof : inftrees_coverage.
Proof.
  intros ty lens1 lens2 lens_ofs codes tbl1 tbl2 table bits work1 work2.
  split; [|split; [|split]]; intros HR; setup HR.
  -
    split; [reflexivity|]. intros Hret. destruct (PR Hret) as (P1 & P2 & P3 & P4 & P5).
    rewrite Z.shiftl_1_l. split; [reflexivity|]. split; [reflexivity|]. split; [exact P1|]. split; [exact P2|]. split.
    + intros i Hi. apply applyw_agree; [exact Ht12 | apply P4; exact Hi | lia].
    + intros i Hi. split; apply applyw_notin; intros Hin; apply in_map_iff in Hin as [[j v] [E Hin]]; cbn in E; subst j;
        apply P3 in Hin; lia.
  -
    intros Hret x Hx. destruct (PR Hret) as (P1 & P2 & P3 & P4 & P5). rewrite Z.shiftl_1_l in *. cbv zeta.
    rewrite Z.shiftl_1_l. intros HM HO.
    assert (SH : entry_shape ty bits' (toff - table) (table + x - table) (arr_get (applyw ws tbl1) (table + x))).
    { apply (applyw_all (fun i v => entry_shape ty bits' (toff - table) (i - table) v)); [exact P5 | apply P4; lia | lia]. }
    replace (table + x - table) with x in SH by lia.
    rewrite may_link_code_op in HM.
    destruct SH as [(s & len & Hs & Hlen & Eop & Eval & _) | [(Hxr & Hbits & Hop & Hv1 & Hv2) | (Eop & _)]].
    + exfalso. rewrite Eop in HM, HO. destruct (sym_entry_nolink ty s Hs) as [E|E]; [exact (HO E) | rewrite E in HM; discriminate HM].
    + rewrite ?Z.shiftl_1_l. repeat split; lia.
    + exfalso. rewrite Eop in HM. cbn in HM. discriminate HM.
  -
    intros Hret i Hi. destruct (PR Hret) as (P1 & P2 & P3 & P4 & P5). rewrite Z.shiftl_1_l in *. cbv zeta. intros HM.
    pose proof (Z.pow_nonneg 2 bits' ltac:(lia)).
    assert (SH : entry_shape ty bits' (toff - table) (i - table) (arr_get (applyw ws tbl1) i)).
    { apply (applyw_all (fun i v => entry_shape ty bits' (toff - table) (i - table) v)); [exact P5 | apply P4; lia | lia]. }
    rewrite may_link_code_op in HM.
    destruct SH as [(s & len & Hs & Hlen & Eop & Eval & _) | [(Hxr & _) | (Eop & _)]].
    + rewrite Eop in HM |- *. destruct (sym_entry_nolink ty s Hs) as [E|E]; [exact E | rewrite E in HM; discriminate HM].
    + exfalso. lia.
    + exfalso. rewrite Eop in HM. cbn in HM. discriminate HM.
  -
    intros Hret Hty' i Hi. subst ty. destruct (PR Hret) as (P1 & P2 & P3 & P4 & P5). cbv zeta. intros Hop.
    assert (SH : entry_shape LENS bits' (toff - table) (i - table) (arr_get (applyw ws tbl1) i)).
    { apply (applyw_all (fun i v => entry_shape LENS bits' (toff - table) (i - table) v)); [exact P5 | apply P4; lia | lia]. }
    destruct SH as [(s & len & Hs & Hlen & Eop & Eval & _) | [(Hxr & Hbits & Hop2 & _) | (Eop & _)]].
    + cbn [sym_entry nsyms] in Hs, Eop, Eval.
      destruct (Z.ltb_spec s 256); [cbn in Eop; lia|]. destruct (Z.eqb_spec s 256); [cbn in Eop; lia|].
      cbn [fst snd] in Eop, Eval. rewrite Eop, Eval in *. apply lens_values_ok; [lia | exact Hop].
    + exfalso. lia.
    + exfalso. lia.
Qed.
End ItProof.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItProof.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeD.

Module RefInflateSafeT.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItProof.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma pow2_pos : forall n, 0 <= n -> 0 < 2 ^ n.
Proof. intros. apply Z.pow_pos_nonneg; lia. Qed.
Lemma pow2_le : forall a b, 0 <= a <= b -> 2 ^ a <= 2 ^ b.
Proof. intros. apply Z.pow_le_mono_r; lia. Qed.
Lemma pow2_lt : forall a b, 0 <= a < b -> 2 ^ a < 2 ^ b.
Proof. intros. apply Z.pow_lt_mono_r; lia. Qed.
Lemma pow2_divide : forall a b, 0 <= a <= b -> (2 ^ a | 2 ^ b).
Proof.
  intros a b H. exists (2 ^ (b - a)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma code_op_nonneg : forall e, 0 <= code_op e.
Proof. intros e. unfold code_op. apply Z.land_nonneg. right. lia. Qed.
Lemma code_bits_nonneg : forall e, 0 <= code_bits e.
Proof. intros e. unfold code_bits. apply Z.land_nonneg. right. lia. Qed.
Lemma code_val_nonneg : forall e, 0 <= code_val e.
Proof. intros e. unfold code_val. apply Z.land_nonneg. right. lia. Qed.

Lemma mod_down : forall a b x y, 0 <= a <= b -> x mod 2 ^ b = y mod 2 ^ b -> x mod 2 ^ a = y mod 2 ^ a.
Proof.
  intros a b x y Hab H.
  rewrite <- (Z.mod_mod_divide x (2 ^ b) (2 ^ a)) by (apply pow2_divide; lia).
  rewrite <- (Z.mod_mod_divide y (2 ^ b) (2 ^ a)) by (apply pow2_divide; lia).
  rewrite H. reflexivity.
Qed.

Lemma mod_small_iff : forall x n, 0 <= n -> 0 <= x < 2 ^ n -> x mod 2 ^ n = x.
Proof. intros. apply Z.mod_small. lia. Qed.

Lemma subidx_range : forall h r o, 0 <= r -> 0 <= o -> 0 <= h mod 2 ^ (r + o) / 2 ^ r < 2 ^ o.
Proof.
  intros h r o Hr Ho. pose proof (pow2_pos r Hr). pose proof (pow2_pos o Ho).
  pose proof (Z.mod_pos_bound h (2 ^ (r + o)) ltac:(apply pow2_pos; lia)) as Hm.
  set (M := h mod 2 ^ (r + o)) in *. clearbody M.
  rewrite Z.pow_add_r in Hm by lia. split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; [lia|]. lia.
Qed.

Lemma subidx_mod : forall h h' r o a b, 0 <= r -> 0 <= o -> 0 <= a -> r + a <= b ->
  h' mod 2 ^ b = h mod 2 ^ b ->
  (h' mod 2 ^ (r + o) / 2 ^ r) mod 2 ^ a = (h mod 2 ^ (r + o) / 2 ^ r) mod 2 ^ a.
Proof.
  intros h h' r o a b Hr Ho Ha Hb E.
  apply Z.bits_inj'. intros i Hi.
  rewrite !Z.testbit_mod_pow2 by lia.
  destruct (Z.ltb_spec i a); [|reflexivity]. cbn [andb].
  rewrite !Z.div_pow2_bits by lia.
  rewrite !Z.testbit_mod_pow2 by lia.
  destruct (Z.ltb_spec (i + r) (r + o)); cbn [andb]; [|reflexivity].
  apply (f_equal (fun z => Z.testbit z (i + r))) in E. rewrite !Z.testbit_mod_pow2 in E by lia.
  replace (i + r <? b) with true in E by (symmetry; apply Z.ltb_lt; lia). exact E.
Qed.

Lemma mod_high : forall h b n, 0 <= h < 2 ^ b -> 0 <= b <= n -> h mod 2 ^ n = h.
Proof.
  intros h b n Hh Hbn. apply Z.mod_small. split; [lia|].
  eapply Z.lt_le_trans; [apply (proj2 Hh)|]. apply pow2_le. lia.
Qed.

Lemma cl_ext_nonneg : forall v, 0 <= cl_ext v <= 7.
Proof. intros v. unfold cl_ext. repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia. Qed.

Lemma land240_small : forall op, 0 <= op <= 15 -> Z.land op 240 = 0.
Proof.
  intros op H. destruct op as [|p|p]; [reflexivity| |lia].
  do 4 (destruct p as [p|p|]; [| |reflexivity]); cbn in H; lia.
Qed.

Lemma sym_entry_not_link : forall ty s, 0 <= s < nsyms ty -> ~ (1 <= fst (sym_entry ty s) <= 15).
Proof.
  intros ty s Hs H. destruct (sym_entry_nolink ty s Hs) as [E|E]; [lia|].
  unfold may_link_op in E. rewrite (land240_small (fst (sym_entry ty s)) ltac:(lia)) in E. cbn in E. discriminate E.
Qed.

Lemma is_linkb_true : forall e, is_linkb e = true <-> 1 <= code_op e <= 15.
Proof. intros e. unfold is_linkb. rewrite Bool.andb_true_iff, !Z.leb_le. tauto. Qed.
Lemma is_linkb_false : forall e, is_linkb e = false <-> ~ (1 <= code_op e <= 15).
Proof. intros e. rewrite <- is_linkb_true. destruct (is_linkb e); split; congruence. Qed.


Section TBLfacts.
  Variable ty : codetype.
Variable get : Z -> Z.
Variable root : Z.
Variable used : Z.
  Hypothesis HT : TBLg ty get root used.

  Lemma T_root : 1 <= root <= 15. Proof. exact (proj1 HT). Qed.
  Lemma T_used : 2 ^ root <= used. Proof. exact (proj1 (proj2 HT)). Qed.
  Lemma T_shape : forall x, 0 <= x < used -> cell_ok ty root used x (get x).
  Proof. exact (proj1 (proj2 (proj2 HT))). Qed.
  Lemma T_rep_root : rep_root get root. Proof. exact (proj1 (proj2 (proj2 (proj2 HT)))). Qed.
  Lemma T_rep_sub : rep_sub get root. Proof. exact (proj2 (proj2 (proj2 (proj2 HT)))). Qed.

  Lemma pow_root_pos : 0 < 2 ^ root. Proof. apply pow2_pos. pose proof T_root. lia. Qed.

  Lemma root_cell : forall x, 0 <= x < 2 ^ root ->
    1 <= code_bits (get x) <= 15
    /\ (is_linkb (get x) = true ->
        code_bits (get x) = root /\ 1 <= code_op (get x) <= 15 - root
        /\ 2 ^ root <= code_val (get x) /\ code_val (get x) + 2 ^ code_op (get x) <= used)
    /\ (is_linkb (get x) = false ->
        code_bits (get x) <= root
        /\ ((exists s, 0 <= s < nsyms ty /\ code_op (get x) = fst (sym_entry ty s) /\ code_val (get x) = snd (sym_entry ty s))
            \/ code_op (get x) = 64)).
  Proof.
    intros x Hx. pose proof T_root as HR. pose proof T_used as HU.
    destruct (T_shape x ltac:(lia)) as [[(s & len & Hs & Hlen & Hop & Hval & [[Hx1 [Hl1 Hb1]]|[Hx2 _]])|[(Hx1 & Hb & Hop & Hv1 & Hv2)|(Hop & Hb & Hv & Hr1)]]|[Hop [[Hx1 Hb]|[Hx2 Hb]]]].
    -
      pose proof (sym_entry_not_link ty s Hs) as NL. rewrite <- Hop in NL.
      split; [lia|]. split.
      + intros L. apply is_linkb_true in L. exfalso. exact (NL L).
      + intros _. split; [lia|]. left. exists s. repeat split; try assumption; lia.
    - exfalso. lia.
    -
      split; [lia|]. split.
      + intros _. repeat split; lia.
      + intros L. apply is_linkb_false in L. exfalso. apply L. lia.
    -
      split; [lia|]. split.
      + intros L. apply is_linkb_true in L. lia.
      + intros _. split; [lia|]. right. exact Hop.
    -
      split; [lia|]. split.
      + intros L. apply is_linkb_true in L. lia.
      + intros _. split; [lia|]. right. exact Hop.
    - exfalso. lia.
  Qed.

  Lemma sub_cell : forall x y, 0 <= x < 2 ^ root -> is_linkb (get x) = true ->
    0 <= y < 2 ^ code_op (get x) ->
    1 <= code_bits (get (code_val (get x) + y)) <= 15 - root
    /\ is_linkb (get (code_val (get x) + y)) = false
    /\ ((exists s, 0 <= s < nsyms ty
                  /\ code_op (get (code_val (get x) + y)) = fst (sym_entry ty s)
                  /\ code_val (get (code_val (get x) + y)) = snd (sym_entry ty s))
        \/ code_op (get (code_val (get x) + y)) = 64).
  Proof.
    intros x y Hx HL Hy. pose proof T_root as HR.
    destruct (root_cell x Hx) as (_ & RL & _). destruct (RL HL) as (Hb & Hop & Hv1 & Hv2).
    set (x' := code_val (get x) + y).
    assert (Hx' : 2 ^ root <= x' < used) by (subst x'; lia).
    pose proof pow_root_pos.
    destruct (T_shape x' ltac:(lia)) as [[(s & len & Hs & Hlen & Hop' & Hval' & [[Hx1 _]|[Hx2 [Hl2 Hb2]]])|[(Hx1 & _)|(Hop' & Hb' & Hv' & Hr1)]]|[Hop' [[Hx1 Hb']|[Hx2 Hb']]]].
    - exfalso. lia.
    - pose proof (sym_entry_not_link ty s Hs) as NL. rewrite <- Hop' in NL.
      split; [lia|]. split; [apply is_linkb_false; exact NL|]. left. exists s. repeat split; try assumption; lia.
    - exfalso. lia.
    - split; [lia|]. split; [apply is_linkb_false; lia|]. right. exact Hop'.
    - exfalso. lia.
    - split; [lia|]. split; [apply is_linkb_false; lia|]. right. exact Hop'.
  Qed.

  Definition rneedg (h : Z) : Z := code_bits (get (h mod 2 ^ root)).
  Definition lneedg (h : Z) : Z :=
    let e := get (h mod 2 ^ root) in
    if is_linkb e
    then code_bits e + code_bits (get (code_val e + h mod 2 ^ (code_bits e + code_op e) / 2 ^ code_bits e))
    else code_bits e.
  Definition cneedg (h : Z) : Z :=
    let e := get (h mod 2 ^ root) in code_bits e + cl_ext (code_val e).

  Lemma ridx_range : forall h, 0 <= h mod 2 ^ root < 2 ^ root.
  Proof. intros h. apply Z.mod_pos_bound. apply pow_root_pos. Qed.

  Lemma rneedg_range : forall h, 1 <= rneedg h <= 15.
  Proof. intros h. unfold rneedg. exact (proj1 (root_cell _ (ridx_range h))). Qed.

  Lemma lneedg_range : forall h, 1 <= lneedg h <= 15 /\ rneedg h <= lneedg h.
  Proof.
    intros h. unfold lneedg, rneedg. pose proof T_root as HR.
    destruct (root_cell _ (ridx_range h)) as (Hb & RL & RN).
    destruct (is_linkb (get (h mod 2 ^ root))) eqn:L.
    - destruct (RL eq_refl) as (Hb2 & Hop & _).
      pose proof (sub_cell (h mod 2 ^ root) (h mod 2 ^ (code_bits (get (h mod 2 ^ root)) + code_op (get (h mod 2 ^ root))) / 2 ^ code_bits (get (h mod 2 ^ root)))
                    (ridx_range h) L ltac:(apply subidx_range; lia)) as (Hs & _). lia.
    - lia.
  Qed.

  Lemma cneedg_range : forall h, 1 <= cneedg h <= 22 /\ rneedg h <= cneedg h.
  Proof.
    intros h. unfold cneedg, rneedg. pose proof (rneedg_range h) as R. unfold rneedg in R.
    pose proof (cl_ext_nonneg (code_val (get (h mod 2 ^ root)))). lia.
  Qed.

  Lemma same_root_idx : forall h h' b, root <= b -> h' mod 2 ^ b = h mod 2 ^ b ->
    h' mod 2 ^ root = h mod 2 ^ root.
  Proof. intros h h' b Hb E. pose proof T_root. apply (mod_down root b); [lia|exact E]. Qed.

  Lemma rep_root_apply : forall h h' b, 0 <= b < root -> h' mod 2 ^ b = h mod 2 ^ b ->
    code_bits (get (h' mod 2 ^ root)) <= b -> get (h mod 2 ^ root) = get (h' mod 2 ^ root).
  Proof.
    intros h h' b Hb E Hle. pose proof T_root as HR.
    destruct (root_cell _ (ridx_range h')) as (Hb' & RL & RN).
    assert (NL : is_linkb (get (h' mod 2 ^ root)) = false).
    { destruct (is_linkb (get (h' mod 2 ^ root))) eqn:L; [|reflexivity]. destruct (RL eq_refl) as (X & _). lia. }
    apply (T_rep_root (h' mod 2 ^ root) (h mod 2 ^ root) (ridx_range h') (ridx_range h) ltac:(lia)).
    set (c := code_bits (get (h' mod 2 ^ root))) in *.
    rewrite !Z.mod_mod_divide by (apply pow2_divide; lia).
    apply (mod_down c b); [lia|]. symmetry. exact E.
  Qed.

  Lemma rneedg_mono : forall h h' b, 0 <= b -> h' mod 2 ^ b = h mod 2 ^ b ->
    b < rneedg h -> b < rneedg h'.
  Proof.
    intros h h' b Hb E Hn. unfold rneedg in *.
    destruct (Z.lt_ge_cases b (code_bits (get (h' mod 2 ^ root)))) as [X|X]; [exact X|]. exfalso.
    destruct (Z.lt_ge_cases b root) as [Br|Br].
    - rewrite (rep_root_apply h h' b ltac:(lia) E X) in Hn. lia.
    - rewrite (same_root_idx h h' b Br E) in X. lia.
  Qed.

  Lemma cneedg_mono : forall h h' b, 0 <= b -> h' mod 2 ^ b = h mod 2 ^ b ->
    b < cneedg h -> b < cneedg h'.
  Proof.
    intros h h' b Hb E Hn. unfold cneedg in *.
    pose proof (cl_ext_nonneg (code_val (get (h' mod 2 ^ root)))).
    destruct (Z.lt_ge_cases b (code_bits (get (h' mod 2 ^ root)))) as [X|X]; [lia|].
    destruct (Z.lt_ge_cases b root) as [Br|Br].
    - rewrite (rep_root_apply h h' b ltac:(lia) E X) in Hn. exact Hn.
    - rewrite (same_root_idx h h' b Br E) in *. exact Hn.
  Qed.

  Lemma lneedg_mono : forall h h' b, 0 <= b -> h' mod 2 ^ b = h mod 2 ^ b ->
    b < lneedg h -> b < lneedg h'.
  Proof.
    intros h h' b Hb E Hn. pose proof T_root as HR.
    pose proof (lneedg_range h') as [R1 R2]. unfold rneedg in R2.
    destruct (Z.lt_ge_cases b (code_bits (get (h' mod 2 ^ root)))) as [X|X]; [lia|].
    destruct (Z.lt_ge_cases b root) as [Br|Br].
    -
      pose proof (rep_root_apply h h' b ltac:(lia) E X) as EQ.
      destruct (root_cell _ (ridx_range h')) as (Hb' & RL & RN).
      assert (NL : is_linkb (get (h' mod 2 ^ root)) = false).
      { destruct (is_linkb (get (h' mod 2 ^ root))) eqn:L; [|reflexivity]. destruct (RL eq_refl) as (Y & _). lia. }
      unfold lneedg in Hn |- *. rewrite EQ, NL in Hn. rewrite NL. exact Hn.
    -
      pose proof (same_root_idx h h' b Br E) as EI.
      unfold lneedg in Hn |- *. rewrite EI in *.
      destruct (is_linkb (get (h mod 2 ^ root))) eqn:L; [|exact Hn].
      destruct (root_cell _ (ridx_range h)) as (Hb0 & RL & _). destruct (RL L) as (Hbr & Hop & Hv1 & Hv2).
      set (e := get (h mod 2 ^ root)) in *.
      set (y := h mod 2 ^ (code_bits e + code_op e) / 2 ^ code_bits e) in *.
      set (y' := h' mod 2 ^ (code_bits e + code_op e) / 2 ^ code_bits e) in *.
      assert (Hy : 0 <= y < 2 ^ code_op e) by (subst y; apply subidx_range; lia).
      assert (Hy' : 0 <= y' < 2 ^ code_op e) by (subst y'; apply subidx_range; lia).
      destruct (Z.lt_ge_cases b (code_bits e + code_bits (get (code_val e + y')))) as [Y|Y]; [exact Y|]. exfalso.
      pose proof (sub_cell (h mod 2 ^ root) y' (ridx_range h) L Hy') as (Sb & _). fold e in Sb.
      assert (EQ : get (code_val e + y) = get (code_val e + y')).
      { apply (T_rep_sub (h mod 2 ^ root) (ridx_range h) ltac:(fold e; lia) y' y Hy' Hy ltac:(fold e; lia)).
        fold e. set (c := code_bits (get (code_val e + y'))) in *.
        subst y y'. symmetry. apply (subidx_mod h h' (code_bits e) (code_op e) c b); try lia. }
      rewrite EQ in Hn. lia.
  Qed.
End TBLfacts.


Lemma decomp_mod : forall x b, 0 <= b -> 0 <= x -> x = x mod 2 ^ b + x / 2 ^ b * 2 ^ b.
Proof. intros x b Hb Hx. pose proof (pow2_pos b Hb). pose proof (Z.div_mod x (2 ^ b) ltac:(lia)). lia. Qed.

Lemma rep_root_b_sound : forall get root, 0 <= root -> rep_root_b get root = true -> rep_root get root.
Proof.
  intros get root Hr H x x' Hx Hx' Hb E. unfold rep_root_b in H.
  pose proof (allz_range 0 (2 ^ root) _ ltac:(rewrite Z.sub_0_r; exact H) x Hx) as Hx0. cbn beta in Hx0.
  set (b := code_bits (get x)) in *.
  replace ((1 <=? b) && (b <=? root)) with true in Hx0 by (symmetry; apply Bool.andb_true_iff; rewrite !Z.leb_le; lia).
  pose proof (pow2_pos b ltac:(lia)) as Pb.
  assert (Hk : 0 <= x' / 2 ^ b < 2 ^ (root - b)).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
    rewrite <- Z.pow_add_r by lia. replace (b + (root - b)) with root by lia. lia. }
  pose proof (allz_range 0 (2 ^ (root - b)) _ ltac:(rewrite Z.sub_0_r; exact Hx0) (x' / 2 ^ b) Hk) as Hk0. cbn beta in Hk0.
  apply Z.eqb_eq in Hk0. rewrite <- E in Hk0. rewrite <- (decomp_mod x' b) in Hk0 by lia. exact Hk0.
Qed.

Lemma rep_sub_b_sound : forall get root, 0 <= root -> rep_sub_b get root = true -> rep_sub get root.
Proof.
  intros get root Hr H x Hx Hop y y' Hy Hy' Hb E. unfold rep_sub_b in H.
  pose proof (allz_range 0 (2 ^ root) _ ltac:(rewrite Z.sub_0_r; exact H) x Hx) as Hx0. cbn beta in Hx0.
  replace ((1 <=? code_op (get x)) && (code_op (get x) <=? 15)) with true in Hx0
    by (symmetry; apply Bool.andb_true_iff; rewrite !Z.leb_le; lia).
  pose proof (allz_range 0 (2 ^ code_op (get x)) _ ltac:(rewrite Z.sub_0_r; exact Hx0) y Hy) as Hy0. cbn beta in Hy0.
  set (b := code_bits (get (code_val (get x) + y))) in *.
  pose proof (pow2_pos b ltac:(lia)) as Pb.
  destruct (Z.lt_ge_cases (code_op (get x)) b) as [Hbo|Hbo].
  {
    assert (y' = y); [|subst y'; reflexivity].
    pose proof (pow2_le (code_op (get x)) b ltac:(lia)).
    rewrite (Z.mod_small y' (2 ^ b)) in E by lia. rewrite (Z.mod_small y (2 ^ b)) in E by lia. exact E. }
  replace ((1 <=? b) && (b <=? code_op (get x))) with true in Hy0 by (symmetry; apply Bool.andb_true_iff; rewrite !Z.leb_le; lia).
  assert (Hk : 0 <= y' / 2 ^ b < 2 ^ (code_op (get x) - b)).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
    rewrite <- Z.pow_add_r by lia. replace (b + (code_op (get x) - b)) with (code_op (get x)) by lia. lia. }
  pose proof (allz_range 0 (2 ^ (code_op (get x) - b)) _ ltac:(rewrite Z.sub_0_r; exact Hy0) (y' / 2 ^ b) Hk) as Hk0. cbn beta in Hk0.
  apply Z.eqb_eq in Hk0. rewrite <- E in Hk0. rewrite <- Z.add_assoc in Hk0. rewrite <- (decomp_mod y' b) in Hk0 by lia. exact Hk0.
Qed.

Lemma tblb_sound : forall ty get root used, tblb ty get root used = true -> TBLg ty get root used.
Proof.
  intros ty get root used H. unfold tblb in H.
  apply andb_prop in H as [H RS]. apply andb_prop in H as [H RR]. apply andb_prop in H as [H SH].
  apply andb_prop in H as [H U]. apply andb_prop in H as [R1 R2].
  apply Z.leb_le in R1. apply Z.leb_le in R2. apply Z.leb_le in U.
  split; [lia|]. split; [exact U|]. split; [|split].
  - intros x Hx. apply cell_ok_b_sound; [lia|].
    exact (allz_range 0 used _ ltac:(rewrite Z.sub_0_r; exact SH) x Hx).
  - apply rep_root_b_sound; [lia|exact RR].
  - apply rep_sub_b_sound; [lia|exact RS].
Qed.

Lemma lenfix_TBLg : TBLg LENS (arr_get lenfix_a) 9 512.
Proof. apply tblb_sound. vm_compute. reflexivity. Qed.

Lemma distfix_TBLg : TBLg DISTS (arr_get distfix_a) 5 32.
Proof. apply tblb_sound. vm_compute. reflexivity. Qed.

Lemma cpok_TBLg : forall ty s p root,
  cpok ty (is_codes s) p root ->
  exists used, TBLg ty (code_at s p) root used
    /\ match p with CDyn ofs => 0 <= ofs /\ ofs + used <= 1444 | CLenfix => used = 512 | CDistfix => used = 32 end.
Proof.
  intros ty s p root H. destruct p as [ofs| |]; cbn [cpok] in H.
  - destruct H as [Ho [used [Hu HT]]]. exists used. split; [exact HT|]. lia.
  - destruct H as [-> ->]. exists 512. split; [exact lenfix_TBLg|reflexivity].
  - destruct H as [-> ->]. exists 32. split; [exact distfix_TBLg|reflexivity].
Qed.

Lemma lneed_lneedg : forall s p root h, lneed s p root h = lneedg (code_at s p) root h.
Proof. reflexivity. Qed.
Lemma cneed_cneedg : forall s h, cneed s h = cneedg (code_at s (is_lencode s)) (is_lenbits s) h.
Proof. reflexivity. Qed.


Definition lens_sym_ok (s : Z) : bool :=
  let '(op, v) := sym_entry LENS s in
  ((op =? 0) && (0 <=? v) && (v <? 256))
  || ((op =? 96) && (v =? 0))
  || ((16 <=? op) && (op <=? 21) && (3 <=? v) && (v + 2 ^ (op - 16) <=? 259))
  || (op =? 203) || (op =? 77).
Lemma lens_sym_cases : forall s, 0 <= s < 288 ->
  let '(op, v) := sym_entry LENS s in
  (op = 0 /\ 0 <= v < 256) \/ (op = 96 /\ v = 0)
  \/ (16 <= op <= 21 /\ 3 <= v /\ v + 2 ^ (op - 16) <= 259) \/ op = 203 \/ op = 77.
Proof.
  intros s Hs.
  pose proof (allz_range 0 288 lens_sym_ok ltac:(vm_compute; reflexivity) s Hs) as H.
  unfold lens_sym_ok in H. destruct (sym_entry LENS s) as [op v].
  repeat (apply Bool.orb_prop in H; destruct H as [H|H]).
  - apply andb_prop in H as [H C]. apply andb_prop in H as [A B].
    apply Z.eqb_eq in A. apply Z.leb_le in B. apply Z.ltb_lt in C. left. lia.
  - apply andb_prop in H as [A B]. apply Z.eqb_eq in A. apply Z.eqb_eq in B. right; left. lia.
  - apply andb_prop in H as [H D]. apply andb_prop in H as [H C]. apply andb_prop in H as [A B].
    apply Z.leb_le in A. apply Z.leb_le in B. apply Z.leb_le in C. apply Z.leb_le in D. right; right; left. lia.
  - apply Z.eqb_eq in H. lia.
  - apply Z.eqb_eq in H. lia.
Qed.

Definition dists_sym_ok (s : Z) : bool :=
  let '(op, v) := sym_entry DISTS s in
  ((16 <=? op) && (op <=? 29) && (1 <=? v) && (v + 2 ^ (op - 16) <=? 32769))
  || ((op =? 64) && (v =? 0)).
Lemma dists_sym_cases : forall s, 0 <= s < 32 ->
  let '(op, v) := sym_entry DISTS s in
  (16 <= op <= 29 /\ 1 <= v /\ v + 2 ^ (op - 16) <= 32769) \/ (op = 64 /\ v = 0).
Proof.
  intros s Hs.
  pose proof (allz_range 0 32 dists_sym_ok ltac:(vm_compute; reflexivity) s Hs) as H.
  unfold dists_sym_ok in H. destruct (sym_entry DISTS s) as [op v].
  apply Bool.orb_prop in H. destruct H as [H|H].
  - apply andb_prop in H as [H D]. apply andb_prop in H as [H C]. apply andb_prop in H as [A B].
    apply Z.leb_le in A. apply Z.leb_le in B. apply Z.leb_le in C. apply Z.leb_le in D. left. lia.
  - apply andb_prop in H as [A B]. apply Z.eqb_eq in A. apply Z.eqb_eq in B. right. lia.
Qed.

Lemma codes_sym : forall s, sym_entry CODES s = (0, s).
Proof. reflexivity. Qed.

Lemma order_a_range : forall k, 0 <= k < 19 -> 0 <= arr_get order_a k < 19.
Proof.
  intros k Hk.
  pose proof (allz_range 0 19 (fun k => (0 <=? arr_get order_a k) && (arr_get order_a k <? 19)) ltac:(vm_compute; reflexivity) k Hk) as H.
  cbn beta in H. apply andb_prop in H as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. lia.
Qed.
Lemma order_a_onto : forall i, 0 <= i < 19 -> exists k, 0 <= k < 19 /\ arr_get order_a k = i.
Proof.
  intros i Hi.
  pose proof (allz_range 0 19 (fun i => anyz 0 19%nat (fun k => arr_get order_a k =? i)) ltac:(vm_compute; reflexivity) i Hi) as H.
  cbn beta in H. destruct (anyz_true _ _ _ H) as [k [Hk E]]. apply Z.eqb_eq in E. exists k. split; [cbn in Hk; lia|exact E].
Qed.


Lemma dist_op_facts : forall op, 16 <= op <= 29 ->
  Z.land op 240 <> 0 /\ Z.land op 64 = 0 /\ Z.land op 15 = op - 16 /\ Z.land op 16 <> 0.
Proof.
  intros op Hop.
  pose proof (allz_range 16 30 (fun op => negb (Z.land op 240 =? 0) && (Z.land op 64 =? 0) && (Z.land op 15 =? op - 16) && negb (Z.land op 16 =? 0))
                ltac:(vm_compute; reflexivity) op ltac:(lia)) as H.
  cbn beta in H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Bool.negb_true_iff in H1. apply Z.eqb_neq in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3.
  apply Bool.negb_true_iff in H4. apply Z.eqb_neq in H4. repeat split; assumption.
Qed.

Lemma len_op_facts : forall op, 16 <= op <= 21 ->
  Z.land op 240 <> 0 /\ Z.land op 64 = 0 /\ Z.land op 15 = op - 16 /\ Z.land op 16 <> 0 /\ Z.land op 32 = 0.
Proof.
  intros op Hop.
  pose proof (allz_range 16 22 (fun op => negb (Z.land op 240 =? 0) && (Z.land op 64 =? 0) && (Z.land op 15 =? op - 16) && negb (Z.land op 16 =? 0) && (Z.land op 32 =? 0))
                ltac:(vm_compute; reflexivity) op ltac:(lia)) as H.
  cbn beta in H. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Bool.negb_true_iff in H1. apply Z.eqb_neq in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3.
  apply Bool.negb_true_iff in H4. apply Z.eqb_neq in H4. apply Z.eqb_eq in H5. repeat split; assumption.
Qed.

Lemma notlink_land240 : forall ty e,
  ((exists sy, 0 <= sy < nsyms ty /\ code_op e = fst (sym_entry ty sy) /\ code_val e = snd (sym_entry ty sy)) \/ code_op e = 64) ->
  ty <> CODES -> code_op e <> 0 -> Z.land (code_op e) 240 <> 0.
Proof.
  intros ty e [[sy (Hsy & Hop & Hv)]|Hop] Hty Hnz.
  - destruct ty; [congruence| |].
    + cbn [nsyms] in Hsy. pose proof (lens_sym_cases sy Hsy) as L.
      destruct (sym_entry LENS sy) as [op v] eqn:Es. cbn [fst snd] in Hop, Hv. rewrite Hop. rewrite Hop in Hnz.
      destruct L as [[L _]|[[L _]|[(L & _)|[L|L]]]]; try lia.
      * rewrite L. discriminate.
      * exact (proj1 (len_op_facts op L)).
      * rewrite L. discriminate.
      * rewrite L. discriminate.
    + cbn [nsyms] in Hsy. pose proof (dists_sym_cases sy Hsy) as L.
      destruct (sym_entry DISTS sy) as [op v] eqn:Es. cbn [fst snd] in Hop, Hv. rewrite Hop.
      destruct L as [(L & _)|[L _]].
      * exact (proj1 (dist_op_facts op L)).
      * rewrite L. discriminate.
  - rewrite Hop. discriminate.
Qed.
End RefInflateSafeT.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.RefInflateSafeT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Ltac sacc :=
  cbn [is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize
       is_whave is_wnext is_window is_window_blk is_hold is_bits is_length is_offset is_extra is_lencode
       is_distcode is_lenbits is_distbits is_ncode is_nlen is_ndist is_have is_next is_lens is_work is_codes
       is_sane is_back is_was is_self_blk is_reqwrap is_reqbits
       iset_mode iset_last iset_wrap iset_havedict iset_flags iset_dmax iset_check iset_total iset_head iset_wbits
       iset_wsize iset_whave iset_wnext iset_window iset_window_blk iset_hold iset_bits iset_length iset_offset
       iset_extra iset_lencode iset_distcode iset_lenbits iset_distbits iset_ncode iset_nlen iset_ndist iset_have
       iset_next iset_lens iset_work iset_codes iset_sane iset_back iset_was iset_self_blk iset_reqwrap iset_reqbits
       ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret
       irset_next irset_have irset_put irset_left irset_hold irset_bits irset_in irset_out irset_ret
       ic_input ic_next_in ic_avail_in ic_outbuf ic_next_out ic_avail_out ic_total_in ic_total_out ic_adler
       ic_data_type ic_msg
       icset_next_in icset_avail_in icset_outbuf icset_next_out icset_avail_out icset_total_in icset_total_out
       icset_adler icset_data_type icset_msg
       w_s w_c w_r wset_s wset_c wset_r fst snd].
Ltac sacc_in H :=
  cbn [is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize
       is_whave is_wnext is_window is_window_blk is_hold is_bits is_length is_offset is_extra is_lencode
       is_distcode is_lenbits is_distbits is_ncode is_nlen is_ndist is_have is_next is_lens is_work is_codes
       is_sane is_back is_was is_self_blk is_reqwrap is_reqbits
       iset_mode iset_last iset_wrap iset_havedict iset_flags iset_dmax iset_check iset_total iset_head iset_wbits
       iset_wsize iset_whave iset_wnext iset_window iset_window_blk iset_hold iset_bits iset_length iset_offset
       iset_extra iset_lencode iset_distcode iset_lenbits iset_distbits iset_ncode iset_nlen iset_ndist iset_have
       iset_next iset_lens iset_work iset_codes iset_sane iset_back iset_was iset_self_blk iset_reqwrap iset_reqbits
       ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret
       irset_next irset_have irset_put irset_left irset_hold irset_bits irset_in irset_out irset_ret
       ic_input ic_next_in ic_avail_in ic_outbuf ic_next_out ic_avail_out ic_total_in ic_total_out ic_adler
       ic_data_type ic_msg
       icset_next_in icset_avail_in icset_outbuf icset_next_out icset_avail_out icset_total_in icset_total_out
       icset_adler icset_data_type icset_msg
       w_s w_c w_r wset_s wset_c wset_r fst snd] in H.

Ltac mred :=
  cbv beta iota delta [MF WF rank Z.eqb Pos.eqb Z.leb Z.compare Pos.compare Pos.compare_cont andb orb
                       HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY
                       TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC].
Ltac mred_in H :=
  cbv beta iota delta [MF WF rank Z.eqb Pos.eqb Z.leb Z.compare Pos.compare Pos.compare_cont andb orb
                       HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY
                       TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC] in H.


Section Rules.
  Context {A B : Type}.

  Lemma POST_bind : forall w0 (m : AM A) (f : A -> AM B) w,
    match m w with
    | ARun a w' => POST w0 (f a w')
    | ALeave w' => WINV w'
    | ARet _ w' => WINV w' /\ INV (w_s w')
    end ->
    POST w0 (abind m f w).
  Proof. intros w0 m f w H. unfold abind. destruct (m w); exact H. Qed.

  Lemma POST_ARun : forall w0 (a : A) w', WINV w' -> PHI w' < PHI w0 -> POST w0 (ARun a w').
  Proof. intros. split; assumption. Qed.
  Lemma POST_ALeave : forall w0 w', WINV w' -> POST w0 (@ALeave A w').
  Proof. intros. assumption. Qed.
  Lemma POST_ARet : forall w0 rc w', WINV w' -> INV (w_s w') -> POST w0 (@ARet A rc w').
  Proof. intros. split; assumption. Qed.

  Lemma POST_weaken : forall w0 w1 (res : ares A), PHI w1 <= PHI w0 -> POST w1 res -> POST w0 res.
  Proof. intros w0 w1 res H HP. destruct res; cbn [POST] in *; [split; [exact (proj1 HP)|lia]|exact HP|exact HP]. Qed.
End Rules.

Lemma gs_eq : forall A (f : inflate_state -> A) s c r, gs f (mkW s c r) = ARun (f s) (mkW s c r). Proof. reflexivity. Qed.
Lemma gc_eq : forall A (f : icall -> A) s c r, gc f (mkW s c r) = ARun (f c) (mkW s c r). Proof. reflexivity. Qed.
Lemma gr_eq : forall A (f : iregs -> A) s c r, gr f (mkW s c r) = ARun (f r) (mkW s c r). Proof. reflexivity. Qed.
Lemma us_eq : forall f s c r, us f (mkW s c r) = ARun tt (mkW (f s) c r). Proof. reflexivity. Qed.
Lemma uc_eq : forall f s c r, uc f (mkW s c r) = ARun tt (mkW s (f c) r). Proof. reflexivity. Qed.
Lemma ur_eq : forall f s c r, ur f (mkW s c r) = ARun tt (mkW s c (f r)). Proof. reflexivity. Qed.
Lemma aret_eq : forall A (a : A) w, aret a w = ARun a w. Proof. reflexivity. Qed.
Lemma aleave_eq : forall A w, @aleave A w = ALeave w. Proof. reflexivity. Qed.
Lemma areturn_eq : forall A rc w, @areturn A rc w = ARet rc w. Proof. reflexivity. Qed.
Lemma aget_eq : forall w, aget w = ARun w w. Proof. reflexivity. Qed.
Lemma amodify_eq : forall f w, amodify f w = ARun tt (f w). Proof. reflexivity. Qed.
Lemma BITS_eq : forall n s c r, BITS n (mkW s c r) = ARun (BITSv (ir_hold r) n) (mkW s c r). Proof. reflexivity. Qed.
Lemma HOLD_eq : forall s c r, HOLD (mkW s c r) = ARun (ir_hold r) (mkW s c r). Proof. reflexivity. Qed.
Lemma DROPBITS_eq : forall n s c r,
  DROPBITS n (mkW s c r) = ARun tt (mkW s c (irset_bits (irset_hold r (Z.shiftr (ir_hold r) n)) (wrap32 (ir_bits r - n)))).
Proof. reflexivity. Qed.
Lemma INITBITS_eq : forall s c r, INITBITS (mkW s c r) = ARun tt (mkW s c (irset_bits (irset_hold r 0) 0)). Proof. reflexivity. Qed.
Lemma BYTEBITS_eq : forall s c r,
  BYTEBITS (mkW s c r) = ARun tt (mkW s c (irset_bits (irset_hold r (Z.shiftr (ir_hold r) (Z.land (ir_bits r) 7))) (wrap32 (ir_bits r - Z.land (ir_bits r) 7)))).
Proof. reflexivity. Qed.
Lemma set_mode_eq : forall m s c r, set_mode m (mkW s c r) = ARun tt (mkW (iset_mode s m) c r). Proof. reflexivity. Qed.
Lemma set_msg_eq : forall m s c r, set_msg m (mkW s c r) = ARun tt (mkW s (icset_msg c m) r). Proof. reflexivity. Qed.
Lemma go_bad_eq : forall m s c r, go_bad m (mkW s c r) = ARun tt (mkW (iset_mode s BAD) (icset_msg c m) r). Proof. reflexivity. Qed.
Lemma set_adler_check_eq : forall v s c r, set_adler_check v (mkW s c r) = ARun tt (mkW (iset_check s v) (icset_adler c v) r).
Proof. reflexivity. Qed.

Ltac pstep lem := apply POST_bind; rewrite lem.


Lemma rank_le3 : forall m, rank m <= 3. Proof. intros m. pose proof (rank_range m). lia. Qed.
Lemma rank_ge0 : forall m, 0 <= rank m. Proof. intros m. pose proof (rank_range m). lia. Qed.


Definition pulled (r r' : iregs) : Prop :=
  exists k, 0 <= k
  /\ ir_next r' = ir_next r + k /\ ir_have r' = ir_have r - k /\ 0 <= ir_have r'
  /\ ir_bits r' = ir_bits r + 8 * k /\ ir_hold r' mod 2 ^ ir_bits r = ir_hold r /\ 0 <= ir_hold r' < 2 ^ ir_bits r'
  /\ ir_put r' = ir_put r /\ ir_left r' = ir_left r /\ ir_in r' = ir_in r /\ ir_out r' = ir_out r /\ ir_ret r' = ir_ret r.

Lemma pulled_refl : forall r, 0 <= ir_have r -> HB (ir_hold r) (ir_bits r) -> pulled r r.
Proof.
  intros r Hhv [Hb Hh]. exists 0. repeat split; try lia. apply Z.mod_small. lia.
Qed.

Lemma pulled_trans : forall r1 r2 r3, 0 <= ir_bits r1 -> pulled r1 r2 -> pulled r2 r3 -> pulled r1 r3.
Proof.
  intros r1 r2 r3 Hb0 (k1 & Hk1 & N1 & H1 & P1 & B1 & M1 & R1 & Q1 & L1 & I1 & O1 & T1)
         (k2 & Hk2 & N2 & H2 & P2 & B2 & M2 & R2 & Q2 & L2 & I2 & O2 & T2).
  exists (k1 + k2). repeat split; try lia.
  rewrite <- M1, <- M2. rewrite B1. symmetry. apply (mod_down (ir_bits r1) (ir_bits r1 + 8 * k1)); [lia|].
  rewrite Z.mod_mod by (apply Z.pow_nonzero; lia). reflexivity.
Qed.

Definition pullr (c : icall) (r : iregs) : iregs :=
  mkIR (ir_next r + 1) (wrap32 (ir_have r - 1)) (ir_put r) (ir_left r)
       (wrap64 (ir_hold r + shl64 (arr_get (ic_input c) (ir_next r)) (ir_bits r))) (wrap32 (ir_bits r + 8))
       (ir_in r) (ir_out r) (ir_ret r).

Lemma PULLBYTE_eq : forall s c r,
  PULLBYTE (mkW s c r) = if ir_have r =? 0 then ALeave (mkW s c r) else ARun tt (mkW s c (pullr c r)).
Proof. reflexivity. Qed.

Lemma pullr_facts : forall c r,
  0 < ir_have r -> ir_have r <= arr_len (ic_input c) -> arr_len (ic_input c) < 2 ^ 32 ->
  0 <= ir_bits r <= 55 -> 0 <= ir_hold r < 2 ^ ir_bits r ->
  0 <= arr_get (ic_input c) (ir_next r) < 256 ->
  ir_next (pullr c r) = ir_next r + 1 /\ ir_have (pullr c r) = ir_have r - 1
  /\ ir_put (pullr c r) = ir_put r /\ ir_left (pullr c r) = ir_left r
  /\ ir_hold (pullr c r) = ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r
  /\ ir_bits (pullr c r) = ir_bits r + 8
  /\ ir_in (pullr c r) = ir_in r /\ ir_out (pullr c r) = ir_out r /\ ir_ret (pullr c r) = ir_ret r
  /\ 0 <= ir_hold (pullr c r) < 2 ^ (ir_bits r + 8)
  /\ ir_hold (pullr c r) mod 2 ^ ir_bits r = ir_hold r.
Proof.
  intros c r Hh Hhl Hn Hb Hho Hby. unfold pullr. cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret].
  assert (Hp : 2 ^ ir_bits r * 2 ^ 8 = 2 ^ (ir_bits r + 8)) by (rewrite <- Z.pow_add_r by lia; reflexivity).
  assert (Hp2 : 2 ^ (ir_bits r + 8) <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia).
  assert (Hsh : shl64 (arr_get (ic_input c) (ir_next r)) (ir_bits r) = arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r).
  { unfold shl64. rewrite Z.shiftl_mul_pow2 by lia. apply wrap64_id. change (2^64) with (2 * 2 ^ 63). nia. }
  rewrite Hsh.
  assert (Hsum : 0 <= ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r < 2 ^ (ir_bits r + 8)) by nia.
  rewrite (wrap64_id (ir_hold r + _)) by (change (2^64) with (2 * 2 ^ 63); lia).
  assert (Hm : (ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r) mod 2 ^ ir_bits r = ir_hold r).
  { rewrite Z.mod_add by (apply Z.pow_nonzero; lia). apply Z.mod_small. lia. }
  rewrite !wrap32_id by lia.
  repeat split; try reflexivity; try lia.
Qed.

Section RegsFacts.
  Variable c : icall.

  Lemma REGS_pullr : forall r, REGS c r -> 0 < ir_have r -> ir_bits r <= 55 ->
    REGS c (pullr c r) /\ pulled r (pullr c r) /\ ir_bits (pullr c r) = ir_bits r + 8 /\ ir_have (pullr c r) = ir_have r - 1.
  Proof.
    intros r HR Hh Hb.
    destruct HR as (N0 & H0 & NH & P0 & L0 & PL & [Bb Bh] & IN & LI & LO).
    destruct (pullr_facts c r Hh ltac:(lia) LI ltac:(lia) Bh (IN _)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
    split; [|split; [|split; [exact E6|exact E2]]].
    - unfold REGS, HB. rewrite E1, E2, E3, E4, E6. repeat split; try lia; apply IN.
    - exists 1. rewrite E1, E2, E3, E4, E6, E7, E8, E9, E11. repeat split; try lia.
  Qed.
End RegsFacts.


Lemma NEEDBITS_k_S : forall k n s c r,
  NEEDBITS_k (S k) n (mkW s c r)
  = if ir_bits r <? n then
      if ir_have r =? 0 then ALeave (mkW s c r) else NEEDBITS_k k n (mkW s c (pullr c r))
    else ARun tt (mkW s c r).
Proof.
  intros.
  change (NEEDBITS_k (S k) n (mkW s c r))
    with (abind (gr ir_bits) (fun bits => if bits <? n then abind PULLBYTE (fun _ => NEEDBITS_k k n) else aret tt) (mkW s c r)).
  unfold abind at 1. cbn [gr w_r]. destruct (ir_bits r <? n); [|reflexivity].
  unfold abind. rewrite PULLBYTE_eq. destruct (ir_have r =? 0); reflexivity.
Qed.

Section Needbits.
  Variable c : icall.

  Lemma NEEDBITS_k_spec : forall k n s r,
    REGS c r -> 0 <= n <= 48 -> n <= ir_bits r + 8 * Z.of_nat k ->
    (exists r', NEEDBITS_k k n (mkW s c r) = ARun tt (mkW s c r')
                /\ REGS c r' /\ pulled r r' /\ n <= ir_bits r' /\ (ir_bits r' = ir_bits r \/ ir_bits r' < n + 8))
    \/ (exists r', NEEDBITS_k k n (mkW s c r) = ALeave (mkW s c r')
                   /\ REGS c r' /\ pulled r r' /\ ir_bits r' < n /\ ir_have r' = 0).
  Proof.
    induction k as [|k IH]; intros n s r HR Hn Hk.
    - left. exists r. cbn [Z.of_nat] in Hk.
      pose proof HR as (_ & H0 & _ & _ & _ & _ & HBr & _ & _ & _).
      split; [reflexivity|]. split; [exact HR|]. split; [apply pulled_refl; [lia|exact HBr]|]. lia.
    - rewrite NEEDBITS_k_S. pose proof HR as (N0 & H0 & NH & P0 & L0 & PL & [Bb Bh] & IN & LI & LO).
      destruct (Z.ltb_spec (ir_bits r) n) as [LT|GE].
      + destruct (Z.eqb_spec (ir_have r) 0) as [Z0|NZ].
        * right. exists r. split; [reflexivity|]. split; [exact HR|]. split; [apply pulled_refl; [lia|split; assumption]|]. lia.
        * destruct (REGS_pullr c r HR ltac:(lia) ltac:(lia)) as (HR1 & HP1 & B1 & _).
          rewrite Nat2Z.inj_succ in Hk.
          destruct (IH n s (pullr c r) HR1 Hn ltac:(lia)) as [(r' & E & HR' & HP' & Hn' & Hb')|(r' & E & HR' & HP' & Hb' & Hh')].
          -- left. exists r'. split; [exact E|]. split; [exact HR'|]. split; [exact (pulled_trans r (pullr c r) r' ltac:(lia) HP1 HP')|].
             split; [exact Hn'|]. right. lia.
          -- right. exists r'. split; [exact E|]. split; [exact HR'|]. split; [exact (pulled_trans r (pullr c r) r' ltac:(lia) HP1 HP')|]. lia.
      + left. exists r. split; [reflexivity|]. split; [exact HR|]. split; [apply pulled_refl; [lia|split; assumption]|]. lia.
  Qed.

  Lemma NEEDBITS_spec : forall n s r,
    REGS c r -> 0 <= n <= 48 ->
    (exists r', NEEDBITS n (mkW s c r) = ARun tt (mkW s c r')
                /\ REGS c r' /\ pulled r r' /\ n <= ir_bits r' /\ (ir_bits r' = ir_bits r \/ ir_bits r' < n + 8))
    \/ (exists r', NEEDBITS n (mkW s c r) = ALeave (mkW s c r')
                   /\ REGS c r' /\ pulled r r' /\ ir_bits r' < n /\ ir_have r' = 0).
  Proof.
    intros n s r HR Hn. unfold NEEDBITS. apply NEEDBITS_k_spec; [exact HR|exact Hn|].
    pose proof HR as (_ & _ & _ & _ & _ & _ & [Bb _] & _ & _ & _). cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
  Qed.
End Needbits.


Lemma BITSv_mod : forall h n, 0 <= h -> 0 <= n <= 32 -> BITSv h n = h mod 2 ^ n.
Proof.
  intros h n Hh Hn. unfold BITSv, zmask, wrap32.
  rewrite Z.shiftl_1_l. change 4294967295 with (Z.ones 32).
  replace (2 ^ n - 1) with (Z.ones n) by (rewrite Z.ones_equiv; lia).
  rewrite !Z.land_ones by lia.
  rewrite (Z.mod_small (Z.ones n)) by (rewrite Z.ones_equiv; pose proof (pow2_le n 32 ltac:(lia)); pose proof (pow2_pos n ltac:(lia)); lia).
  rewrite Z.land_ones by lia. apply Z.mod_mod_divide. apply pow2_divide. lia.
Qed.

Lemma DECODE_k_O : forall p index need s c r,
  DECODE_k O p index need (mkW s c r) = ARun (code_at s p (index (ir_hold r))) (mkW s c r).
Proof. reflexivity. Qed.
Lemma DECODE_k_S : forall k p index need s c r,
  DECODE_k (S k) p index need (mkW s c r)
  = if need (code_at s p (index (ir_hold r))) <=? ir_bits r then ARun (code_at s p (index (ir_hold r))) (mkW s c r)
    else if ir_have r =? 0 then ALeave (mkW s c r) else DECODE_k k p index need (mkW s c (pullr c r)).
Proof.
  intros. cbn [DECODE_k]. unfold abind, HOLD, gr, gs. cbn [w_r w_s].
  destruct (need (code_at s p (index (ir_hold r))) <=? ir_bits r); [reflexivity|].
  rewrite PULLBYTE_eq. destruct (ir_have r =? 0); reflexivity.
Qed.

Section Decode.
  Variable c : icall.
  Variable s : inflate_state.
Variable p : codeptr.
Variable ty : codetype.
Variable root : Z.
Variable used : Z.
  Hypothesis HT : TBLg ty (code_at s p) root used.

  Let HR15 := T_root ty (code_at s p) root used HT.

  Lemma pulled_mod : forall r r' b, pulled r r' -> 0 <= ir_hold r < 2 ^ ir_bits r -> 0 <= b <= ir_bits r ->
    ir_hold r' mod 2 ^ b = ir_hold r mod 2 ^ b.
  Proof.
    intros r r' b (k & Hk & _ & _ & _ & B & M & _) Hh Hb.
    apply (mod_down b (ir_bits r)); [lia|]. rewrite M. symmetry. apply Z.mod_small. lia.
  Qed.

  Lemma DECODE1_k_spec : forall k r,
    REGS c r -> 15 < ir_bits r + 8 * Z.of_nat k ->
    (exists r' here, DECODE_k k p (fun hold => BITSv hold root) code_bits (mkW s c r) = ARun here (mkW s c r')
       /\ REGS c r' /\ pulled r r' /\ here = code_at s p (ir_hold r' mod 2 ^ root)
       /\ code_bits here <= ir_bits r' /\ (ir_bits r' = ir_bits r \/ ir_bits r' < code_bits here + 8))
    \/ (exists r', DECODE_k k p (fun hold => BITSv hold root) code_bits (mkW s c r) = ALeave (mkW s c r')
       /\ REGS c r' /\ pulled r r' /\ ir_have r' = 0 /\ ir_bits r' < rneedg (code_at s p) root (ir_hold r')).
  Proof.
    induction k as [|k IH]; intros r HR Hk; pose proof HR as (N0 & H0 & NH & P0 & L0 & PL & [Bb Bh] & IN & LI & LO).
    - left. rewrite DECODE_k_O. rewrite (BITSv_mod (ir_hold r) root) by lia.
      eexists r, _. split; [reflexivity|]. split; [exact HR|]. split; [apply pulled_refl; [lia|split; assumption]|].
      split; [reflexivity|]. cbn [Z.of_nat] in Hk.
      pose proof (rneedg_range ty (code_at s p) root used HT (ir_hold r)) as RR. unfold rneedg in RR. lia.
    - rewrite DECODE_k_S. rewrite (BITSv_mod (ir_hold r) root) by lia.
      pose proof (rneedg_range ty (code_at s p) root used HT (ir_hold r)) as RR. unfold rneedg in RR.
      destruct (Z.leb_spec (code_bits (code_at s p (ir_hold r mod 2 ^ root))) (ir_bits r)) as [LE|GT].
      + left. eexists r, _. split; [reflexivity|]. split; [exact HR|]. split; [apply pulled_refl; [lia|split; assumption]|].
        split; [reflexivity|]. lia.
      + destruct (Z.eqb_spec (ir_have r) 0) as [Z0|NZ].
        * right. exists r. split; [reflexivity|]. split; [exact HR|]. split; [apply pulled_refl; [lia|split; assumption]|].
          split; [exact Z0|]. unfold rneedg. lia.
        * destruct (REGS_pullr c r HR ltac:(lia) ltac:(lia)) as (HR1 & HP1 & B1 & _).
          rewrite Nat2Z.inj_succ in Hk.
          assert (MONO : forall r', pulled r r' -> ir_bits r < rneedg (code_at s p) root (ir_hold r')).
          { intros r' HP'. apply (rneedg_mono ty (code_at s p) root used HT (ir_hold r)); [lia| |unfold rneedg; lia].
            apply (pulled_mod r r'); [exact HP'|lia|lia]. }
          destruct (IH (pullr c r) HR1 ltac:(lia)) as [(r' & here & E & HR' & HP' & Eh & Hle & Hb')|(r' & E & HR' & HP' & Hh' & Hb')].
          -- left. exists r', here. split; [exact E|]. split; [exact HR'|].
             pose proof (pulled_trans r (pullr c r) r' ltac:(lia) HP1 HP') as HP.
             split; [exact HP|]. split; [exact Eh|]. split; [exact Hle|]. right.
             pose proof (MONO r' HP) as M. unfold rneedg in M. rewrite <- Eh in M. lia.
          -- right. exists r'. split; [exact E|]. split; [exact HR'|].
             split; [exact (pulled_trans r (pullr c r) r' ltac:(lia) HP1 HP')|]. split; [exact Hh'|exact Hb'].
  Qed.

  Lemma DECODE1_spec : forall r, REGS c r ->
    (exists r' here, DECODE1 p root (mkW s c r) = ARun here (mkW s c r')
       /\ REGS c r' /\ pulled r r' /\ here = code_at s p (ir_hold r' mod 2 ^ root)
       /\ code_bits here <= ir_bits r' /\ (ir_bits r' = ir_bits r \/ ir_bits r' < code_bits here + 8))
    \/ (exists r', DECODE1 p root (mkW s c r) = ALeave (mkW s c r')
       /\ REGS c r' /\ pulled r r' /\ ir_have r' = 0 /\ ir_bits r' < rneedg (code_at s p) root (ir_hold r')).
  Proof.
    intros r HR. unfold DECODE1. apply DECODE1_k_spec; [exact HR|].
    pose proof HR as (_ & _ & _ & _ & _ & _ & [Bb _] & _ & _ & _). cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
  Qed.

  Definition subix (last h : Z) : Z := code_val last + h mod 2 ^ (code_bits last + code_op last) / 2 ^ code_bits last.

  Lemma DECODE2_k_spec : forall k r last,
    REGS c r -> 15 < ir_bits r + 8 * Z.of_nat k ->
    last = code_at s p (ir_hold r mod 2 ^ root) -> is_linkb last = true -> code_bits last <= ir_bits r ->
    (exists r' here, DECODE_k k p (fun hold => code_val last + Z.shiftr (BITSv hold (code_bits last + code_op last)) (code_bits last))
                                  (fun here => wrap32 (code_bits last + code_bits here)) (mkW s c r) = ARun here (mkW s c r')
       /\ REGS c r' /\ pulled r r' /\ here = code_at s p (subix last (ir_hold r'))
       /\ 1 <= code_bits here <= 15 - root
       /\ code_bits last + code_bits here <= ir_bits r' /\ (ir_bits r' = ir_bits r \/ ir_bits r' < code_bits last + code_bits here + 8))
    \/ (exists r', DECODE_k k p (fun hold => code_val last + Z.shiftr (BITSv hold (code_bits last + code_op last)) (code_bits last))
                            (fun here => wrap32 (code_bits last + code_bits here)) (mkW s c r) = ALeave (mkW s c r')
       /\ REGS c r' /\ pulled r r' /\ ir_have r' = 0 /\ ir_bits r' < lneedg (code_at s p) root (ir_hold r')).
  Proof.
    induction k as [|k IH]; intros r last HR Hk El HL Hlb; pose proof HR as (N0 & H0 & NH & P0 & L0 & PL & [Bb Bh] & IN & LI & LO).
    - pose proof (ridx_range ty (code_at s p) root used HT (ir_hold r)) as XR.
      destruct (root_cell ty (code_at s p) root used HT _ XR) as (_ & RL & _). rewrite <- El in RL.
      destruct (RL HL) as (Lb & Lop & Lv1 & Lv2).
      assert (IX : forall h, 0 <= h -> code_val last + Z.shiftr (BITSv h (code_bits last + code_op last)) (code_bits last) = subix last h).
      { intros h Hh. unfold subix. rewrite Z.shiftr_div_pow2 by lia. rewrite BITSv_mod by lia. reflexivity. }
      assert (SUB : forall h, 0 <= h -> 1 <= code_bits (code_at s p (subix last h)) <= 15 - root).
      { intros h Hh. unfold subix. rewrite El.
        apply (sub_cell ty (code_at s p) root used HT); [exact XR|rewrite <- El; exact HL|]. rewrite <- El. apply subidx_range; lia. }
      left. rewrite DECODE_k_O. rewrite IX by lia.
      eexists r, _. split; [reflexivity|]. split; [exact HR|]. split; [apply pulled_refl; [lia|split; assumption]|].
      split; [reflexivity|]. split; [apply SUB; lia|]. cbn [Z.of_nat] in Hk. pose proof (SUB (ir_hold r) ltac:(lia)). lia.
    - pose proof (ridx_range ty (code_at s p) root used HT (ir_hold r)) as XR.
      destruct (root_cell ty (code_at s p) root used HT _ XR) as (_ & RL & _). rewrite <- El in RL.
      destruct (RL HL) as (Lb & Lop & Lv1 & Lv2).
      assert (IX : forall h, 0 <= h -> code_val last + Z.shiftr (BITSv h (code_bits last + code_op last)) (code_bits last) = subix last h).
      { intros h Hh. unfold subix. rewrite Z.shiftr_div_pow2 by lia. rewrite BITSv_mod by lia. reflexivity. }
      assert (SUB : forall h, 0 <= h -> 1 <= code_bits (code_at s p (subix last h)) <= 15 - root).
      { intros h Hh. unfold subix. rewrite El.
        apply (sub_cell ty (code_at s p) root used HT); [exact XR|rewrite <- El; exact HL|]. rewrite <- El. apply subidx_range; lia. }
      assert (LN : forall r', pulled r r' -> lneedg (code_at s p) root (ir_hold r') = code_bits last + code_bits (code_at s p (subix last (ir_hold r')))).
      { intros r' HP'. unfold lneedg.
        rewrite (pulled_mod r r' root HP' ltac:(lia) ltac:(lia)). rewrite <- El, HL. reflexivity. }
      rewrite DECODE_k_S. rewrite IX by lia.
      pose proof (SUB (ir_hold r) ltac:(lia)) as SB.
      rewrite (wrap32_id (code_bits last + _)) by lia.
      destruct (Z.leb_spec (code_bits last + code_bits (code_at s p (subix last (ir_hold r)))) (ir_bits r)) as [LE|GT].
      + left. eexists r, _. split; [reflexivity|]. split; [exact HR|]. split; [apply pulled_refl; [lia|split; assumption]|].
        split; [reflexivity|]. split; [exact SB|]. lia.
      + destruct (Z.eqb_spec (ir_have r) 0) as [Z0|NZ].
        * right. exists r. split; [reflexivity|]. split; [exact HR|].
          assert (HP0 : pulled r r) by (apply pulled_refl; [lia|split; assumption]).
          split; [exact HP0|]. split; [exact Z0|]. rewrite (LN r HP0). lia.
        * destruct (REGS_pullr c r HR ltac:(lia) ltac:(lia)) as (HR1 & HP1 & B1 & _).
          rewrite Nat2Z.inj_succ in Hk.
          assert (MONO : forall r', pulled r r' -> ir_bits r < lneedg (code_at s p) root (ir_hold r')).
          { intros r' HP'. apply (lneedg_mono ty (code_at s p) root used HT (ir_hold r)); [lia| |].
            - apply (pulled_mod r r'); [exact HP'|lia|lia].
            - rewrite (LN r ltac:(apply pulled_refl; [lia|split; assumption])). lia. }
          assert (El1 : last = code_at s p (ir_hold (pullr c r) mod 2 ^ root)).
          { rewrite (pulled_mod r (pullr c r) root HP1 ltac:(lia) ltac:(lia)). exact El. }
          destruct (IH (pullr c r) last HR1 ltac:(lia) El1 HL ltac:(lia))
            as [(r' & here & E & HR' & HP' & Eh & Hsb & Hle & Hb')|(r' & E & HR' & HP' & Hh' & Hb')].
          -- left. exists r', here. split; [exact E|]. split; [exact HR'|].
             pose proof (pulled_trans r (pullr c r) r' ltac:(lia) HP1 HP') as HP.
             split; [exact HP|]. split; [exact Eh|]. split; [exact Hsb|]. split; [exact Hle|]. right.
             pose proof (MONO r' HP) as M. rewrite (LN r' HP) in M. rewrite <- Eh in M. lia.
          -- right. exists r'. split; [exact E|]. split; [exact HR'|].
             split; [exact (pulled_trans r (pullr c r) r' ltac:(lia) HP1 HP')|]. split; [exact Hh'|exact Hb'].
  Qed.

  Lemma DECODE2_spec : forall r last,
    REGS c r -> last = code_at s p (ir_hold r mod 2 ^ root) -> is_linkb last = true -> code_bits last <= ir_bits r ->
    (exists r' here, DECODE2 p last (mkW s c r) = ARun here (mkW s c r')
       /\ REGS c r' /\ pulled r r' /\ here = code_at s p (subix last (ir_hold r'))
       /\ 1 <= code_bits here <= 15 - root
       /\ code_bits last + code_bits here <= ir_bits r' /\ (ir_bits r' = ir_bits r \/ ir_bits r' < code_bits last + code_bits here + 8))
    \/ (exists r', DECODE2 p last (mkW s c r) = ALeave (mkW s c r')
       /\ REGS c r' /\ pulled r r' /\ ir_have r' = 0 /\ ir_bits r' < lneedg (code_at s p) root (ir_hold r')).
  Proof.
    intros r last HR El HL Hlb. unfold DECODE2. apply DECODE2_k_spec; try assumption.
    pose proof HR as (_ & _ & _ & _ & _ & _ & [Bb _] & _ & _ & _). cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
  Qed.
End Decode.
