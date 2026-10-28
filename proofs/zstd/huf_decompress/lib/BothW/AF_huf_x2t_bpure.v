(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas ZdHufStats ZdHufX1 ZdHufX2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_x2t_hdefs AF_huf_x2t_bdefs AF_huf_x1t_bpure.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition x2prf (T c : Z) (ks : list Z) (dt : list Z) : Prop := x2pref T c dt /\ forall k, In k ks -> 0 <= k /\ c2ok T dt (c + k).

Lemma x2prf_open : forall T c dt, x2pref T c dt -> x2prf T c [] dt.
Proof. intros T c dt P. split; [exact P|]. intros k []. Qed.

Lemma c2ok_upd_other : forall T dt u j v, c2ok T dt u -> 0 <= u -> 0 <= j -> (j < 4 * u + 6 \/ 4 * u + 8 <= j) -> c2ok T (Zupd j v dt) u.
Proof. intros T dt u j v [A B] Hu Hj0 Hj. split; rewrite Znth_Zupd_other by lia; assumption. Qed.

Lemma prf2_st_sq : forall T c ks dt k i a b, x2prf T c ks dt -> 0 <= c -> 0 <= k -> i = 4 + 4 * (c + k) ->
  x2prf T c ks (Zupd (i + 1) b (Zupd i a dt)).
Proof.
  intros T c ks dt k i a b [P K] Hc Hk ->. split.
  - intros u Hu. apply c2ok_upd_other; [apply c2ok_upd_other; [apply P; lia| lia| lia| lia] | lia| lia| lia].
  - intros k' IN. destruct (K k' IN) as [K0 KV]. split; [exact K0|].
    apply c2ok_upd_other; [apply c2ok_upd_other; [exact KV| lia| lia| lia] | lia| lia| lia].
Qed.
Lemma prf2_st_sq1 : forall T c ks dt k i a, x2prf T c ks dt -> 0 <= c -> 0 <= k -> (i = 4 + 4 * (c + k) \/ i = 4 + 4 * (c + k) + 1) ->
  x2prf T c ks (Zupd i a dt).
Proof.
  intros T c ks dt k i a [P K] Hc Hk Hi. split.
  - intros u Hu. apply c2ok_upd_other; [apply P; lia| lia| lia| lia].
  - intros k' IN. destruct (K k' IN) as [K0 KV]. split; [exact K0|]. apply c2ok_upd_other; [exact KV| lia| lia| lia].
Qed.
Lemma prf2_st_nl : forall T c ks dt k i nb ln, x2prf T c ks dt -> 0 <= c -> 0 <= k -> i = 4 + 4 * (c + k) + 2 -> i + 1 < Z.of_nat (length dt) ->
  0 <= nb <= T -> 1 <= ln <= 2 ->
  x2prf T c (k :: ks) (Zupd (i + 1) ln (Zupd i nb dt)).
Proof.
  intros T c ks dt k i nb ln [P K] Hc Hk -> HL Hnb Hln. unfold FseNCount.Zlength in *. split.
  - intros u Hu. apply c2ok_upd_other; [apply c2ok_upd_other; [apply P; lia| lia| lia| lia] | lia| lia| lia].
  - intros k' [<-|IN].
    + split; [lia|]. split.
      * replace (4 * (c + k) + 6) with (4 + 4 * (c + k) + 2) by lia. rewrite Znth_Zupd_other by lia. rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; lia). exact Hnb.
      * replace (4 * (c + k) + 7) with (4 + 4 * (c + k) + 2 + 1) by lia. rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; rewrite Zupd_length; lia). exact Hln.
    + destruct (K k' IN) as [K0 KV]. split; [exact K0|].
      destruct (Z.eq_dec k' k) as [->|NE].
      * split.
        -- replace (4 * (c + k) + 6) with (4 + 4 * (c + k) + 2) by lia. rewrite Znth_Zupd_other by lia. rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; lia). exact Hnb.
        -- replace (4 * (c + k) + 7) with (4 + 4 * (c + k) + 2 + 1) by lia. rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; rewrite Zupd_length; lia). exact Hln.
      * apply c2ok_upd_other; [apply c2ok_upd_other; [exact KV| lia| lia| lia] | lia| lia| lia].
Qed.
Lemma prf2_close : forall T c ks dt L, x2prf T c ks dt -> 0 <= c -> (forall k, 0 <= k < L -> In k ks) -> x2pref T (c + L) dt.
Proof.
  intros T c ks dt L [P K] Hc COV u Hu. destruct (Z.lt_ge_cases u c) as [LT|GE]; [apply P; lia|].
  replace u with (c + (u - c)) by lia. apply (fun IN => proj2 (K _ IN)). apply COV. lia.
Qed.
Lemma prf2_close_c : forall T c ks dt (L : nat), x2prf T c ks dt -> 0 <= c -> cover L ks = true -> x2pref T (c + Z.of_nat L) dt.
Proof. intros T c ks dt L P Hc C. apply (prf2_close T c ks dt); [exact P | exact Hc | apply cover_ok; exact C]. Qed.

Lemma x2pref_upd_hi : forall T cur dt j v, x2pref T cur dt -> 4 + 4 * cur <= j -> x2pref T cur (Zupd j v dt).
Proof. intros T cur dt j v P Hj u Hu. apply c2ok_upd_other; [apply P; lia| lia| lia| lia]. Qed.
Lemma x2pref_mono : forall T a b dt, x2pref T b dt -> a <= b -> x2pref T a dt.
Proof. intros T a b dt P H u Hu. apply P. lia. Qed.
Lemma x2pref_upd_hdr : forall T cur dt j v, x2pref T cur dt -> 0 <= j < 4 -> x2pref T cur (Zupd j v dt).
Proof. intros T cur dt j v P Hj u Hu. apply c2ok_upd_other; [apply P; lia| lia| lia| lia]. Qed.
Lemma x2pref_T_le : forall T T' cur dt, x2pref T cur dt -> T <= T' -> x2pref T' cur dt.
Proof. intros T T' cur dt P H u Hu. destruct (P u Hu) as [A B]. split; lia. Qed.

Definition d1_chk : bool :=
  forallb (fun nb => forallb (fun s =>
    let X := Z.lor (65536 * nb + 16777216) s in
    (X mod 256 =? s) && ((X / 256) mod 256 =? 0) && ((X / 65536) mod 256 =? nb) && ((X / 65536 / 256) mod 256 =? 1) && (X / 65536 =? nb + 256) && (X =? 65536 * nb + 16777216 + s))
    (bzseq 256 0)) (bzseq 13 0).
Lemma d1_chk_ok : d1_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma d1_bytes : forall nb s, 0 <= nb <= 12 -> 0 <= s < 256 ->
  Z.lor (65536 * nb + 16777216) s mod 256 = s /\ (Z.lor (65536 * nb + 16777216) s / 256) mod 256 = 0
  /\ (Z.lor (65536 * nb + 16777216) s / 65536) mod 256 = nb /\ (Z.lor (65536 * nb + 16777216) s / 65536 / 256) mod 256 = 1
  /\ Z.lor (65536 * nb + 16777216) s / 65536 = nb + 256 /\ Z.lor (65536 * nb + 16777216) s = 65536 * nb + 16777216 + s.
Proof.
  intros nb s Hnb Hs. pose proof d1_chk_ok as C. unfold d1_chk in C. rewrite forallb_forall in C.
  specialize (C nb ltac:(apply bzseq_In_iff; lia)). rewrite forallb_forall in C. specialize (C s ltac:(apply bzseq_In_iff; lia)).
  cbv beta in C. repeat (apply andb_prop in C; destruct C as [C ?C1]).
  repeat match goal with H : (_ =? _) = true |- _ => apply Z.eqb_eq in H end. repeat split; assumption.
Qed.

Section F.
  Variables (hw rank : list Z) (nbs tl mtl : Z).
  Hypothesis STATS : huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl.
  Hypothesis NBSR : 2 <= nbs <= 256.
  Hypothesis LHW : zlen hw = 256.
  Hypothesis BHW : Forall isbyte hw.
  Hypothesis LRK : zlen rank = 13.
  Hypothesis TLM : tl <= mtl.
  Hypothesis MTL : mtl <= 12.
  Notation TT := (TTB tl mtl).
  Notation XS1 w := (xs1 rank w).
  Notation WS := (firstn (Z.to_nat nbs) hw).

  Lemma TT_range' : 1 <= tl <= 12 -> tl <= TT <= mtl /\ Z.min mtl 11 <= TT.
  Proof. intros H. apply TTB_range; lia. Qed.
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

  Definition RINV (w : Z) (rs0 : list Z) : Prop := forall v, 1 <= v < w -> Znth (v + 1) rs0 = XS1 v.

  Section M.
  Variable maxW : Z.
  Hypothesis HMW : 1 <= maxW <= tl.
  Hypothesis HIGH : forall v, maxW < v <= 12 -> Znth v rank = 0.

  Definition PS (w : Z) : Z := if w =? 0 then XS1 (maxW + 1) else XS1 w.
  Definition SINV (i : Z) (rs0 : list Z) : Prop := forall w, 0 <= w <= maxW -> Znth (w + 1) rs0 = PS w + hcount (firstn (Z.to_nat i) WS) w.

  Lemma ws_len : FseNCount.Zlength WS = nbs.
  Proof. unfold FseNCount.Zlength. rewrite length_firstn. lia. Qed.
  Lemma ws_nth : forall i, 0 <= i < nbs -> Znth i WS = Znth i hw.
  Proof.
    intros i Hi. unfold Znth. rewrite <- (firstn_skipn (Z.to_nat nbs) hw) at 2.
    rewrite app_nth1 by (rewrite length_firstn; lia). reflexivity.
  Qed.
  Lemma sinv0 : forall rs0, RINV (maxW + 1) rs0 -> Znth 1 rs0 = XS1 (maxW + 1) -> SINV 0 rs0.
  Proof.
    intros rs0 RI R1 w Hw. change (Z.to_nat 0) with 0%nat. rewrite firstn_O. unfold hcount. cbn [count_occ]. rewrite Z.add_0_r.
    unfold PS. destruct (Z.eqb_spec w 0) as [->|NE]; [exact R1|]. apply RI. lia.
  Qed.
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
  Lemma sinv_end : forall rs0, SINV nbs rs0 -> forall w, 1 <= w <= maxW -> Znth (w + 1) rs0 = XS1 (w + 1).
  Proof.
    intros rs0 SI w Hw. rewrite (SI w ltac:(lia)). rewrite <- ws_len at 1. rewrite hcount_firstn_all.
    pose proof STATS as (TLR & _ & _ & _ & CNT & _). rewrite <- (CNT w ltac:(lia)). unfold PS.
    destruct (Z.eqb_spec w 0); [lia|]. rewrite (xs1_step rank w) by lia. reflexivity.
  Qed.

  Definition RSF (rs0 : list Z) : Prop := forall w, 1 <= w <= maxW + 1 -> Znth w rs0 = XS1 w.
  Lemma rsf_of_sinv : forall rs0, SINV nbs rs0 -> zlen rs0 = 15 -> RSF (Zupd 1 0 rs0).
  Proof.
    intros rs0 SI RL w Hw. destruct (Z.eq_dec w 1) as [->|NE].
    - rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; lia). rewrite (xs1_1 rank). reflexivity.
    - rewrite Znth_Zupd_other by lia. replace w with ((w - 1) + 1) at 1 by lia. rewrite (sinv_end rs0 SI (w - 1)) by lia. f_equal. lia.
  Qed.

  Notation RV0 w := (rv0 rank tl TT w).
  Lemma rv0_bounds : forall w, 1 <= w <= maxW + 1 -> 0 <= RV0 w <= 2 ^ mtl /\ RV0 (maxW + 1) = 2^TT.
  Proof.
    intros w Hw. pose proof STATS as (TLR & _). pose proof (TT_range' TLR) as TTR.
    pose proof (rv0_top (firstn (Z.to_nat nbs) hw) rank tl TT STATS ltac:(lia) maxW HMW HIGH) as TOP.
    pose proof (rv0_nonneg (firstn (Z.to_nat nbs) hw) rank tl TT STATS ltac:(lia) w ltac:(lia)).
    pose proof (rv0_mono (firstn (Z.to_nat nbs) hw) rank tl TT STATS ltac:(lia) w (maxW + 1) ltac:(lia) ltac:(lia)).
    assert (2^TT <= 2^mtl) by (apply Z.pow_le_mono_r; lia). lia.
  Qed.
  Definition VINV (w : Z) (rv : list Z) : Prop := forall v, 1 <= v < w -> Znth v rv = RV0 v.

  Notation RVC c w := (rvc rank tl TT c w).
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
  Definition RVX (rv : list Z) : Prop :=
    (forall v, 1 <= v <= maxW -> Znth v rv = RV0 v) /\
    (forall c v, tl + 1 - maxW <= c <= TT - (tl + 1 - maxW) -> 1 <= v <= maxW -> Znth (13 * c + v) rv = RVC c v).
  Lemma rvx_of_rows : forall rv, ROWS (TT - (tl + 1 - maxW) + 1) 1 rv -> RVX rv.
  Proof. intros rv (R0 & RC & _). split; [exact R0|]. intros c v Hc Hv. apply RC; lia. Qed.

  Lemma l1_facts : forall w e, 1 <= w <= maxW -> e = TT - (tl + 1 - w) -> 0 <= e ->
    0 <= XS1 w /\ XS1 (w + 1) <= 256 /\ XS1 (w + 1) = XS1 w + Znth w rank /\ 0 <= Znth w rank /\ 0 <= RV0 w
    /\ RV0 (w + 1) = RV0 w + Znth w rank * 2 ^ e /\ RV0 (w + 1) <= 2 ^ mtl /\ 1 <= 2 ^ e <= 2 ^ mtl.
  Proof.
    intros w e Hw He H0. pose proof STATS as (TLR & _). pose proof (TT_range' TLR) as TTR.
    pose proof (xs1_bounds' w ltac:(lia)). pose proof (xs1_bounds' (w + 1) ltac:(lia)). pose proof (xs1_step rank w ltac:(lia)).
    pose proof (rank_small' w ltac:(lia)).
    pose proof (rv0_bounds w ltac:(lia)) as [R0 _]. pose proof (rv0_bounds (w + 1) ltac:(lia)) as [R1 _].
    pose proof (rv0_step rank tl TT ltac:(lia) w ltac:(lia)) as ST1. replace (TT - (tl + 1 - w)) with e in ST1 by lia.
    assert (1 <= 2 ^ e) by (apply (Z.pow_le_mono_r 2 0 e); lia).
    assert (2 ^ e <= 2 ^ mtl) by (apply Z.pow_le_mono_r; lia).
    repeat split; lia.
  Qed.

  Lemma l2x_facts : forall w len minW, 1 <= w <= maxW -> tl - maxW + 1 <= TT - (tl + 1 - w) -> len = 2 ^ (TT - (tl + 1 - w)) ->
    minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) ->
    RV0 (w + 1) = RV0 w + (XS1 (w + 1) - XS1 w) * len /\ 2 <= len <= 2 ^ (mtl - 1) /\ 1 <= minW <= maxW /\ tl + 1 - w + (tl + 1 - TT) <= minW
    /\ RVC (tl + 1 - w) (maxW + 1) = len /\ 0 <= RVC (tl + 1 - w) minW <= len /\ RVC (tl + 1 - w) 1 = 0.
  Proof.
    intros w len minW HW HE HL HMN. pose proof STATS as (TLR & _). pose proof (TT_range' TLR) as TTR.
    destruct (l1_facts w (TT - (tl + 1 - w)) HW ltac:(lia) ltac:(lia)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
    rewrite <- HL in F6.
    assert (L2 : 2 <= len <= 2 ^ (mtl - 1)) by (rewrite HL; split; [change 2 with (2 ^ 1) at 1; apply Z.pow_le_mono_r; lia| apply Z.pow_le_mono_r; lia]).
    pose proof (rvc_top (firstn (Z.to_nat nbs) hw) rank tl TT STATS ltac:(lia) (tl + 1 - w) maxW ltac:(lia) HMW HIGH) as TOP.
    rewrite <- HL in TOP.
    pose proof (rvc_nonneg (firstn (Z.to_nat nbs) hw) rank tl TT STATS ltac:(lia) (tl + 1 - w) minW ltac:(lia) ltac:(lia)) as N0.
    pose proof (rvc_mono (firstn (Z.to_nat nbs) hw) rank tl TT STATS ltac:(lia) (tl + 1 - w) minW (maxW + 1) ltac:(lia) ltac:(lia) ltac:(lia)) as MO.
    pose proof (rvc_1 rank tl TT (tl + 1 - w) ltac:(lia)) as R1.
    repeat split; try lia.
  Qed.

  Lemma w2_facts : forall w len minW w2 len2, 1 <= w <= maxW -> tl - maxW + 1 <= TT - (tl + 1 - w) -> len = 2 ^ (TT - (tl + 1 - w)) ->
    minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) -> minW <= w2 <= maxW -> len2 = 2 ^ (TT - (tl + 1 - w) - (tl + 1 - w2)) ->
    0 <= XS1 w2 /\ XS1 (w2 + 1) <= 256 /\ XS1 (w2 + 1) = XS1 w2 + Znth w2 rank /\ 0 <= Znth w2 rank
    /\ 0 <= RVC (tl + 1 - w) w2 /\ RVC (tl + 1 - w) (w2 + 1) = RVC (tl + 1 - w) w2 + (XS1 (w2 + 1) - XS1 w2) * len2 /\ RVC (tl + 1 - w) (w2 + 1) <= len
    /\ 1 <= len2 <= len /\ 0 <= TT - (tl + 1 - w) - (tl + 1 - w2) <= mtl - 1 /\ RVC (tl + 1 - w) w2 <= len.
  Proof.
    intros w len minW w2 len2 HW HE HL HMN HW2 HL2. pose proof STATS as (TLR & _). pose proof (TT_range' TLR) as TTR.
    destruct (l2x_facts w len minW HW HE HL HMN) as (G6 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof (xs1_bounds' w2 ltac:(lia)). pose proof (xs1_bounds' (w2 + 1) ltac:(lia)).
    pose proof (xs1_step rank w2 ltac:(lia)). pose proof (rank_small' w2 ltac:(lia)).
    pose proof (rvc_nonneg (firstn (Z.to_nat nbs) hw) rank tl TT STATS ltac:(lia) (tl + 1 - w) w2 ltac:(lia) ltac:(lia)) as N0.
    pose proof (rvc_step rank tl TT ltac:(lia) (tl + 1 - w) w2 ltac:(lia) ltac:(lia) ltac:(lia)) as ST.
    replace (TT - (tl + 1 - w2) - (tl + 1 - w)) with (TT - (tl + 1 - w) - (tl + 1 - w2)) in ST by lia. rewrite <- HL2 in ST.
    pose proof (rvc_mono (firstn (Z.to_nat nbs) hw) rank tl TT STATS ltac:(lia) (tl + 1 - w) (w2 + 1) (maxW + 1) ltac:(lia) ltac:(lia) ltac:(lia)) as MO. rewrite G11 in MO.
    pose proof (rvc_mono (firstn (Z.to_nat nbs) hw) rank tl TT STATS ltac:(lia) (tl + 1 - w) w2 (maxW + 1) ltac:(lia) ltac:(lia) ltac:(lia)) as MO2. rewrite G11 in MO2.
    assert (E2 : 0 <= TT - (tl + 1 - w) - (tl + 1 - w2) <= mtl - 1) by lia.
    assert (1 <= len2) by (rewrite HL2; apply (Z.pow_le_mono_r 2 0); lia).
    assert (len2 <= len) by (rewrite HL2, HL; apply Z.pow_le_mono_r; lia).
    repeat split; lia.
  Qed.
  End M.
End F.
