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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItGen.
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
