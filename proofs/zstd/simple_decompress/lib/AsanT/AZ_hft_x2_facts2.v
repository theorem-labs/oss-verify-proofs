(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdHufX2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AZ_hft_x2_defs AZ_hft_x2_facts.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).
Notation isbyte := (fun v : Z => 0 <= v < 256).

Section F.
  Variables (hw rank : list Z) (nbs tl : Z).
  Hypothesis STATS : huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl.
  Hypothesis NBSR : 2 <= nbs <= 256.
  Hypothesis LHW : zlen hw = 256.
  Hypothesis BHW : Forall isbyte hw.
  Hypothesis LRK : zlen rank = 13.
  Notation TT := (AZ_hft_x2_defs.TT tl).
  Notation XS1 w := (xs1 rank w).
  Notation RV0 w := (rv0 rank tl TT w).
  Notation RVC c w := (rvc rank tl TT c w).

  Section M.
  Variable maxW : Z.
  Hypothesis HMW : 1 <= maxW <= tl.
  Hypothesis HIGH : forall v, maxW < v <= 12 -> Znth v rank = 0.

  (* [comment removed for export] *)
  Lemma TT_range : 1 <= tl <= 12 -> tl <= TT <= 12 /\ 11 <= TT.
  Proof. intros H. unfold AZ_hft_x2_defs.TT. destruct (Z.ltb_spec tl 12); lia. Qed.
  Lemma rank_small : forall v, 0 <= v <= 12 -> 0 <= Znth v rank <= 256.
  Proof. intros. eapply AZ_hft_x2_facts.rank_small'; eauto. Qed.
  Lemma xs1_bounds : forall w, 1 <= w <= 13 -> 0 <= XS1 w <= 256.
  Proof. intros. eapply AZ_hft_x2_facts.xs1_bounds'; eauto. Qed.
  Lemma l1_facts : forall w e, 1 <= w <= maxW -> e = TT - (tl + 1 - w) -> 0 <= e ->
    0 <= XS1 w /\ XS1 (w + 1) <= 256 /\ XS1 (w + 1) = XS1 w + Znth w rank /\ 0 <= Znth w rank /\ 0 <= RV0 w
    /\ RV0 (w + 1) = RV0 w + Znth w rank * 2 ^ e /\ RV0 (w + 1) <= 4096 /\ 1 <= 2 ^ e <= 4096.
  Proof. intros. eapply AZ_hft_x2_facts.l1_facts; eauto. Qed.

  (* [comment removed for export] *)
  Lemma l2x_facts : forall w len minW, 1 <= w <= maxW -> tl - maxW + 1 <= TT - (tl + 1 - w) -> len = 2 ^ (TT - (tl + 1 - w)) ->
    minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) ->
    RV0 (w + 1) = RV0 w + (XS1 (w + 1) - XS1 w) * len /\ 2 <= len <= 2048 /\ 1 <= minW <= maxW /\ tl + 1 - w + (tl + 1 - TT) <= minW
    /\ RVC (tl + 1 - w) (maxW + 1) = len /\ 0 <= RVC (tl + 1 - w) minW <= len /\ RVC (tl + 1 - w) 1 = 0.
  Proof.
    intros w len minW HW HE HL HMN. pose proof STATS as (TLR & _). pose proof (TT_range TLR) as TTR.
    destruct (l1_facts w (TT - (tl + 1 - w)) HW ltac:(lia) ltac:(lia)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
    rewrite <- HL in F6.
    assert (L2 : 2 <= len <= 2048) by (rewrite HL; split; [change 2 with (2 ^ 1) at 1; apply Z.pow_le_mono_r; lia| change 2048 with (2 ^ 11); apply Z.pow_le_mono_r; lia]).
    pose proof (rvc_top (firstn (Z.to_nat nbs) hw) rank tl TT STATS ltac:(lia) (tl + 1 - w) maxW ltac:(lia) HMW HIGH) as TOP.
    replace (TT - (tl + 1 - w)) with (TT - (tl + 1 - w)) in TOP by lia. rewrite <- HL in TOP.
    pose proof (rvc_nonneg (firstn (Z.to_nat nbs) hw) rank tl TT STATS ltac:(lia) (tl + 1 - w) minW ltac:(lia) ltac:(lia)) as N0.
    pose proof (rvc_mono (firstn (Z.to_nat nbs) hw) rank tl TT STATS ltac:(lia) (tl + 1 - w) minW (maxW + 1) ltac:(lia) ltac:(lia) ltac:(lia)) as MO.
    pose proof (rvc_1 rank tl TT (tl + 1 - w) ltac:(lia)) as R1.
    repeat split; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma w2_facts : forall w len minW w2 len2, 1 <= w <= maxW -> tl - maxW + 1 <= TT - (tl + 1 - w) -> len = 2 ^ (TT - (tl + 1 - w)) ->
    minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) -> minW <= w2 <= maxW -> len2 = 2 ^ (TT - (tl + 1 - w) - (tl + 1 - w2)) ->
    0 <= XS1 w2 /\ XS1 (w2 + 1) <= 256 /\ XS1 (w2 + 1) = XS1 w2 + Znth w2 rank /\ 0 <= Znth w2 rank
    /\ 0 <= RVC (tl + 1 - w) w2 /\ RVC (tl + 1 - w) (w2 + 1) = RVC (tl + 1 - w) w2 + (XS1 (w2 + 1) - XS1 w2) * len2 /\ RVC (tl + 1 - w) (w2 + 1) <= len
    /\ 1 <= len2 <= len /\ 0 <= TT - (tl + 1 - w) - (tl + 1 - w2) <= 11 /\ RVC (tl + 1 - w) w2 <= len.
  Proof.
    intros w len minW w2 len2 HW HE HL HMN HW2 HL2. pose proof STATS as (TLR & _). pose proof (TT_range TLR) as TTR.
    destruct (l2x_facts w len minW HW HE HL HMN) as (G6 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof (xs1_bounds w2 ltac:(lia)). pose proof (xs1_bounds (w2 + 1) ltac:(lia)).
    pose proof (xs1_step rank w2 ltac:(lia)). pose proof (rank_small w2 ltac:(lia)).
    pose proof (rvc_nonneg (firstn (Z.to_nat nbs) hw) rank tl TT STATS ltac:(lia) (tl + 1 - w) w2 ltac:(lia) ltac:(lia)) as N0.
    pose proof (rvc_step rank tl TT ltac:(lia) (tl + 1 - w) w2 ltac:(lia) ltac:(lia) ltac:(lia)) as ST.
    replace (TT - (tl + 1 - w2) - (tl + 1 - w)) with (TT - (tl + 1 - w) - (tl + 1 - w2)) in ST by lia. rewrite <- HL2 in ST.
    pose proof (rvc_mono (firstn (Z.to_nat nbs) hw) rank tl TT STATS ltac:(lia) (tl + 1 - w) (w2 + 1) (maxW + 1) ltac:(lia) ltac:(lia) ltac:(lia)) as MO. rewrite G11 in MO.
    pose proof (rvc_mono (firstn (Z.to_nat nbs) hw) rank tl TT STATS ltac:(lia) (tl + 1 - w) w2 (maxW + 1) ltac:(lia) ltac:(lia) ltac:(lia)) as MO2. rewrite G11 in MO2.
    assert (E2 : 0 <= TT - (tl + 1 - w) - (tl + 1 - w2) <= 11) by lia.
    assert (1 <= len2) by (rewrite HL2; apply (Z.pow_le_mono_r 2 0); lia).
    assert (len2 <= len) by (rewrite HL2, HL; apply Z.pow_le_mono_r; lia).
    repeat split; lia.
  Qed.
  End M.
End F.
