(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdHufX2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AZ_hft_x2_defs.
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
  Notation WS := (firstn (Z.to_nat nbs) hw).

  Lemma TT_range' : 1 <= tl <= 12 -> tl <= TT <= 12 /\ 11 <= TT.
  Proof. intros H. unfold AZ_hft_x2_defs.TT. destruct (Z.ltb_spec tl 12); lia. Qed.
  Lemma rank_small' : forall v, 0 <= v <= 12 -> 0 <= Znth v rank <= 256.
  Proof.
    intros v Hv. destruct STATS as (_ & (_ & LENW) & _ & _ & CNT & _). rewrite (CNT v Hv). unfold hcount.
    pose proof (count_occ_bound Z.eq_dec v (firstn (Z.to_nat nbs) hw)) as CB. unfold FseNCount.Zlength in LENW. lia.
  Qed.
  Lemma xs1_bounds' : forall w, 1 <= w <= 13 -> 0 <= XS1 w <= 256.
  Proof.
    intros w Hw. pose proof STATS as (_ & (_ & LENW) & _). unfold FseNCount.Zlength in LENW.
    pose proof (xs1_nonneg (firstn (Z.to_nat nbs) hw) rank tl STATS w Hw) as A.
    pose proof (xs1_mono (firstn (Z.to_nat nbs) hw) rank tl STATS w 13 ltac:(lia) ltac:(lia)) as B.
    pose proof (xs1_top (firstn (Z.to_nat nbs) hw) rank tl STATS) as C.
    pose proof (rank_small' 0 ltac:(lia)). unfold FseNCount.Zlength in C. rewrite length_firstn in C. lia.
  Qed.

  (* [comment removed for export] *)
  Definition RINV (w : Z) (rs0 : list Z) : Prop := forall v, 1 <= v < w -> Znth (v + 1) rs0 = XS1 v.

  Section M.
  Variable maxW : Z.
  Hypothesis HMW : 1 <= maxW <= tl.
  Hypothesis HIGH : forall v, maxW < v <= 12 -> Znth v rank = 0.

  (* [comment removed for export] *)
  Definition PS (w : Z) : Z := if w =? 0 then XS1 (maxW + 1) else XS1 w.
  Definition SINV (i : Z) (rs0 : list Z) : Prop := forall w, 0 <= w <= maxW -> Znth (w + 1) rs0 = PS w + hcount (firstn (Z.to_nat i) WS) w.

  Lemma ws_len : FseNCount.Zlength WS = nbs.
  Proof. unfold FseNCount.Zlength. rewrite length_firstn. lia. Qed.
  Lemma ws_nth : forall i, 0 <= i < nbs -> Znth i WS = Znth i hw.
  Proof.
    intros i Hi. unfold Znth. rewrite <- (firstn_skipn (Z.to_nat nbs) hw) at 2.
    rewrite app_nth1 by (rewrite length_firstn; lia). reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma sinv0 : forall rs0, RINV (maxW + 1) rs0 -> Znth 1 rs0 = XS1 (maxW + 1) -> SINV 0 rs0.
  Proof.
    intros rs0 RI R1 w Hw. change (Z.to_nat 0) with 0%nat. rewrite firstn_O. unfold hcount. cbn [count_occ]. rewrite Z.add_0_r.
    unfold PS. destruct (Z.eqb_spec w 0) as [->|NE]; [exact R1|]. apply RI. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma sort_unit : forall j rs0, 0 <= j < nbs -> SINV j rs0 -> zlen rs0 = 15 ->
    0 <= Znth j hw <= maxW /\ 0 <= Znth (Znth j hw + 1) rs0 /\ Znth (Znth j hw + 1) rs0 + 1 <= nbs
    /\ SINV (j + 1) (Zupd (Znth j hw + 1) (Znth (Znth j hw + 1) rs0 + 1) rs0).
  Proof.
    intros j rs0 Hj SI RL. pose proof ws_len as WSL. pose proof (ws_nth j Hj) as WNTH.
    pose proof (hcount_firstn_lt WS j ltac:(rewrite WSL; lia)) as HLT. pose proof (hcount_firstn_step WS j) as HST.
    pose proof (hcount_nonneg (firstn (Z.to_nat j) WS) (Znth j WS)) as H0.
    pose proof STATS as (TLR & _ & FA & _ & CNT & _).
    pose proof (hForall_Znth _ WS j FA ltac:(rewrite WSL; lia)) as WR0. cbv beta in WR0.
    rewrite WNTH in HLT, HST, H0, WR0. set (w := Znth j hw) in *.
    rewrite <- (CNT w ltac:(lia)) in HLT.
    assert (WM1 : w <= maxW) by (destruct (Z_le_gt_dec w maxW) as [L|G]; [exact L | exfalso; rewrite (HIGH w ltac:(lia)) in HLT; lia]).
    pose proof (SI w ltac:(lia)) as RV.
    assert (SLOT : 0 <= Znth (w + 1) rs0 /\ Znth (w + 1) rs0 + 1 <= nbs).
    { rewrite RV. unfold PS. pose proof (xs1_total WS rank tl STATS maxW ltac:(lia) HIGH) as XT. rewrite WSL in XT.
      destruct (Z.eqb_spec w 0) as [E0|N0].
      - pose proof (xs1_nonneg WS rank tl STATS (maxW + 1) ltac:(lia)). rewrite E0 in *. lia.
      - pose proof (xs1_nonneg WS rank tl STATS w ltac:(lia)). pose proof (xs1_step rank w ltac:(lia)) as XS.
        pose proof (xs1_mono WS rank tl STATS (w + 1) (maxW + 1) ltac:(lia) ltac:(lia)). pose proof (rank_small' 0 ltac:(lia)). lia. }
    split; [lia|]. split; [lia|]. split; [lia|].
    intros v Hv. rewrite (HST v ltac:(rewrite WSL; lia)). destruct (Z.eq_dec w v) as [<-|NE].
    - rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; lia). rewrite RV. lia.
    - rewrite Znth_Zupd_other by lia. rewrite (SI v Hv). lia.
  Qed.
  (* [comment removed for export] *)
  Lemma sinv_end : forall rs0, SINV nbs rs0 -> forall w, 1 <= w <= maxW -> Znth (w + 1) rs0 = XS1 (w + 1).
  Proof.
    intros rs0 SI w Hw. rewrite (SI w ltac:(lia)). rewrite <- ws_len at 1. rewrite hcount_firstn_all.
    pose proof STATS as (TLR & _ & _ & _ & CNT & _). rewrite <- (CNT w ltac:(lia)). unfold PS.
    destruct (Z.eqb_spec w 0); [lia|]. rewrite (xs1_step rank w) by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition RSF (rs0 : list Z) : Prop := forall w, 1 <= w <= maxW + 1 -> Znth w rs0 = XS1 w.
  Lemma rsf_of_sinv : forall rs0, SINV nbs rs0 -> zlen rs0 = 15 -> RSF (Zupd 1 0 rs0).
  Proof.
    intros rs0 SI RL w Hw. destruct (Z.eq_dec w 1) as [->|NE].
    - rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; lia). rewrite (xs1_1 rank). reflexivity.
    - rewrite Znth_Zupd_other by lia. replace w with ((w - 1) + 1) at 1 by lia. rewrite (sinv_end rs0 SI (w - 1)) by lia. f_equal. lia.
  Qed.

  Notation RV0 w := (rv0 rank tl TT w).
  Lemma rv0_bounds : forall w, 1 <= w <= maxW + 1 -> 0 <= RV0 w <= 4096 /\ RV0 (maxW + 1) = 2^TT.
  Proof.
    intros w Hw. pose proof STATS as (TLR & _). pose proof (TT_range' TLR) as TTR.
    pose proof (rv0_top (firstn (Z.to_nat nbs) hw) rank tl TT STATS ltac:(lia) maxW HMW HIGH) as TOP.
    pose proof (rv0_nonneg (firstn (Z.to_nat nbs) hw) rank tl TT STATS ltac:(lia) w ltac:(lia)).
    pose proof (rv0_mono (firstn (Z.to_nat nbs) hw) rank tl TT STATS ltac:(lia) w (maxW + 1) ltac:(lia) ltac:(lia)).
    assert (2^TT <= 2^12) by (apply Z.pow_le_mono_r; lia). change (2^12) with 4096 in *. lia.
  Qed.
  Definition VINV (w : Z) (rv : list Z) : Prop := forall v, 1 <= v < w -> Znth v rv = RV0 v.

  Notation RVC c w := (rvc rank tl TT c w).
  (* [comment removed for export] *)
  Definition ROWS (c w : Z) (rv : list Z) : Prop :=
    (forall v, 1 <= v <= maxW -> Znth v rv = RV0 v) /\
    (forall c' v, tl + 1 - maxW <= c' < c -> 1 <= v <= maxW -> Znth (13 * c' + v) rv = RVC c' v) /\
    (forall v, 1 <= v < w -> Znth (13 * c + v) rv = RVC c v).
  Lemma rows0 : forall c rv, c <= tl + 1 - maxW -> VINV (maxW + 1) rv -> ROWS c 1 rv.
  Proof. intros c rv Hc VI. split; [intros v Hv; apply VI; lia|]. split; intros; lia. Qed.
  Lemma rows_next : forall c rv, ROWS c (maxW + 1) rv -> ROWS (c + 1) 1 rv.
  Proof.
    intros c rv (R0 & RC & RWW). split; [exact R0|]. split; [| intros; lia].
    intros c' v Hc Hv. destruct (Z.eq_dec c' c) as [->|NE]; [apply RWW; lia | apply RC; lia].
  Qed.
  Lemma rvc_val : forall c w, 0 <= c -> 1 <= w <= maxW + 1 -> 0 <= RVC c w <= RV0 w /\ RVC c w = RV0 w / 2^c.
  Proof.
    intros c w Hc Hw. pose proof (rv0_bounds w Hw) as (RB & _). unfold rvc. fold (RV0 w).
    assert (0 < 2^c) by (apply Z.pow_pos_nonneg; lia).
    split; [| reflexivity]. split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia|nia]].
  Qed.
  (* [comment removed for export] *)
  Definition RVX (rv : list Z) : Prop :=
    (forall v, 1 <= v <= maxW -> Znth v rv = RV0 v) /\
    (forall c v, tl + 1 - maxW <= c <= TT - (tl + 1 - maxW) -> 1 <= v <= maxW -> Znth (13 * c + v) rv = RVC c v).
  Lemma rvx_of_rows : forall rv, ROWS (TT - (tl + 1 - maxW) + 1) 1 rv -> RVX rv.
  Proof. intros rv (R0 & RC & _). split; [exact R0|]. intros c v Hc Hv. apply RC; lia. Qed.

  (* [comment removed for export] *)
  Lemma l1_facts : forall w e, 1 <= w <= maxW -> e = TT - (tl + 1 - w) -> 0 <= e ->
    0 <= XS1 w /\ XS1 (w + 1) <= 256 /\ XS1 (w + 1) = XS1 w + Znth w rank /\ 0 <= Znth w rank /\ 0 <= RV0 w
    /\ RV0 (w + 1) = RV0 w + Znth w rank * 2 ^ e /\ RV0 (w + 1) <= 4096 /\ 1 <= 2 ^ e <= 4096.
  Proof.
    intros w e Hw He H0. pose proof STATS as (TLR & _). pose proof (TT_range' TLR) as TTR.
    pose proof (xs1_bounds' w ltac:(lia)). pose proof (xs1_bounds' (w + 1) ltac:(lia)). pose proof (xs1_step rank w ltac:(lia)).
    pose proof (rank_small' w ltac:(lia)).
    pose proof (rv0_bounds w ltac:(lia)) as [R0 _]. pose proof (rv0_bounds (w + 1) ltac:(lia)) as [R1 _].
    pose proof (rv0_step rank tl TT ltac:(lia) w ltac:(lia)) as ST1. replace (TT - (tl + 1 - w)) with e in ST1 by lia.
    assert (1 <= 2 ^ e) by (apply (Z.pow_le_mono_r 2 0 e); lia).
    assert (2 ^ e <= 2 ^ 12) by (apply Z.pow_le_mono_r; lia). change (2 ^ 12) with 4096 in *.
    repeat split; lia.
  Qed.
  End M.
End F.
