(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import MngRepr MngImage MngHeap MngSurgery MngNtfPre.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AXG_ffpost MngMeta.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Section G.
Variables (R : option (sptr * Z)) (U : Z -> Z) (s : astate).
Hypothesis HI : Inv [] R U s.

#[using="R U HI"] Lemma ufacts : forall q a, usedX [] s q a -> 16 <= stride_of a /\ 0 <= am_last a <= 31 /\ 0 <= poff (am_mem a).
Proof. LiaFast.lf_pins (fun (R U HI : LiaFast.U) => LiaFast.u0).
  intros q a Hu. pose proof (stride_pos _ _ _ _ _ (inv_groups HI q a Hu)) as S.
  pose proof (inv_groups HI q a Hu) as ((Gl & _) & _). destruct (used_group_region [] R U s q a HI Hu) as (rg & _ & _ & _ & Ho & _). lia.
Qed.

#[using="R U HI"] Lemma ext28 : forall q a, usedX [] s q a -> 28 <= group_extent a.
Proof. LiaFast.lf_pins (fun (R U HI : LiaFast.U) => LiaFast.u0). intros q a Hu. destruct (ufacts q a Hu) as (S & L & _). unfold group_extent, UNIT, IB. nia. Qed.

#[using="Type"] Lemma st_mono : forall a i j, 0 <= stride_of a -> i <= j -> poff (slot_start a i) <= poff (slot_start a j).
Proof. LiaFast.lf_pins LiaFast.u0. intros a i j Hs Hij. rewrite !poff_slot_start. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. Qed.

#[using="Type"] Lemma st_last : forall a, poff (slot_start a (am_last a)) + stride_of a - IB = poff (am_mem a) + group_extent a.
Proof. LiaFast.lf_pins LiaFast.u0. intros a. rewrite poff_slot_start. unfold group_extent. ring. Qed.

(* [comment removed for export] *)
#[using="R U HI"] Theorem adjacency_impossible : forall h ah q aq, usedX [] s h ah -> usedX [] s q aq -> h <> q ->
  prid (am_mem ah) = prid (am_mem aq) -> poff (am_mem ah) + group_extent ah = poff (am_mem aq) -> False.
Proof. LiaFast.lf_pins (fun (R U HI : LiaFast.U) => LiaFast.u0).
  intros h ah q aq Uh Uq Hne Er Eo.
  destruct (ufacts h ah Uh) as (Sh & Lh & Oh). destruct (ufacts q aq Uq) as (Sq & Lq & Oq).
  pose proof (extent_pos _ _ _ _ _ (inv_groups HI h ah Uh)) as Xh.
  pose proof (inv_groups HI q aq Uq) as (_ & _ & _ & _ & Gmp & Gns).
  destruct (Z.eq_dec (am_maplen aq) 0) as [Hml|Hml].
  2:{ destruct (used_group_region [] R U s q aq HI Uq) as (rg & _ & _ & _ & _ & _ & Z0). rewrite (Z0 ltac:(pose proof (inv_groups HI q aq Uq) as (_ & Gml & _); lia)) in Eo. lia. }
  destruct (Gns Hml) as (_ & p & ap & k & fr & Up & Hk & Hfr & Kfr & Emem & _ & _ & _).
  destruct (ufacts p ap Up) as (Sp & Lp & Op).
  pose proof (f_equal poff Emem) as Eoq. pose proof (f_equal prid Emem) as Erq. rewrite prid_slot_start in Erq.
  pose proof (st_last ah) as ELh.
  destruct (sptr_eq_dec h p) as [<-|Hhp].
  - pose proof (usedX_fun _ _ _ _ _ Up Uh) as ->.
    pose proof (st_mono ah k (am_last ah) ltac:(lia) ltac:(lia)) as M. unfold IB in ELh. lia.
  - assert (Erp : prid (am_mem ah) = prid (am_mem ap)) by congruence.
    pose proof (slot_in_span [] R U s HI p ap k Up Hk) as [SP1 SP2].
    destruct (inv_laminar HI h ah p ap Uh Up Hhp Erp) as [D | [I | I]].
    + unfold spans_disjoint in D. unfold UNIT, IB in *. lia.
    + destruct (inside_slot_start [] R U s HI h ah (am_last ah) p ap Uh Up ltac:(lia) I) as (j & fr' & Hj & _ & _ & A & B).
      destruct (Z.eq_dec k j) as [->|Hkj]; [unfold UNIT, IB in *; lia|].
      destruct (same_group_starts ap k j Hkj Sp); unfold UNIT, IB in *; lia.
    + destruct (inside_slot_start [] R U s HI p ap k h ah Up Uh Hk I) as (j & fr' & Hj & _ & _ & A & B).
      pose proof (st_mono ah j (am_last ah) ltac:(lia) ltac:(lia)) as M. unfold UNIT, IB in *. lia.
Qed.

(* [comment removed for export] *)
#[using="R U HI"] Theorem markers_vs_hdr : forall c q aq, In c (markers s) -> MT s q = Some (MUsed aq) ->
  exists qc, mc_loc c = LMem qc /\
    (prid qc <> prid (am_mem aq) \/ poff qc + Z.of_nat (mc_w c) <= poff (am_mem aq) \/ poff (am_mem aq) + 12 <= poff qc).
Proof. LiaFast.lf_pins (fun (R U HI : LiaFast.U) => LiaFast.u0).
  intros c q aq Hc Mq.
  assert (ND : List.NoDup (keys s)) by exact (proj1 (inv_keys HI)).
  assert (Uq : usedX [] s q aq) by (apply usedX_intro; [reflexivity | exact Mq]).
  destruct (ufacts q aq Uq) as (Sq & Lq & Oq).
  pose proof (extent_pos _ _ _ _ _ (inv_groups HI q aq Uq)) as Xq.
  destruct (In_markers_inv s c Hc) as [(h & ah & j & fr & HF & Kfr & Hc') | (h & ah & Hu & ->)].
  - destruct (in_frames_inv s h ah j fr HF) as (Hu & Hj & Hfr).
    assert (Uh : usedX [] s h ah) by (apply usedX_intro; [reflexivity | exact (proj1 (used_metas_iff s h ah ND) Hu)]).
    destruct (ufacts h ah Uh) as (Sh & Lh & Oh).
    pose proof (inv_groups HI h ah Uh) as (_ & _ & Gsl & _). pose proof (Gsl j Hj) as (_ & _ & S3). rewrite Hfr in S3.
    destruct S3 as (_ & _ & (N0 & O0 & F0 & _) & _).
    destruct (marker_cells_span ah j fr c ltac:(lia) N0 F0 Hc') as (qc & Eq & Hq1 & Hq2 & Hq3).
    exists qc. split; [exact Eq|].
    destruct (Nat.eq_dec (prid qc) (prid (am_mem aq))) as [Erc|Erc]; [|left; exact Erc]. right.
    rewrite Hq1, prid_slot_start in Erc.
    pose proof (slot_in_span [] R U s HI h ah j Uh Hj) as [SJ1 SJ2].
    destruct (sptr_eq_dec h q) as [<-|Hhq].
    + pose proof (usedX_fun _ _ _ _ _ Uq Uh) as ->. right. unfold UNIT, IB in *. lia.
    + destruct (inv_laminar HI h ah q aq Uh Uq Hhq Erc) as [D | [I | I]].
      * unfold spans_disjoint in D. destruct D as [D|D]; [|right; unfold UNIT, IB in *; lia].
        destruct (Z.eq_dec (poff (am_mem ah) + group_extent ah) (poff (am_mem aq))) as [E|E].
        -- exfalso. exact (adjacency_impossible h ah q aq Uh Uq Hhq Erc E).
        -- left. unfold UNIT, IB in *. lia.
      * destruct (inside_slot_start [] R U s HI h ah j q aq Uh Uq Hj I) as (k & fr' & Hk & _ & _ & A & B).
        pose proof (slot_in_span [] R U s HI q aq k Uq Hk) as [SK1 _]. right. unfold UNIT, IB in *. lia.
      * destruct (inside_slot_start [] R U s HI q aq 0 h ah Uq Uh ltac:(lia) I) as (k & fr' & Hk & Hfr' & Kfr' & A & B).
        pose proof (poff_slot_start aq 0) as E0. rewrite Z.mul_0_r in E0.
        destruct (Z.eq_dec k j) as [->|Hkj].
        -- exfalso. rewrite Hfr in Hfr'. injection Hfr' as <-. rewrite Kfr in Kfr'. discriminate.
        -- destruct (same_group_starts ah k j Hkj Sh); unfold UNIT, IB in *; lia.
  - assert (Uh : usedX [] s h ah) by (apply usedX_intro; [reflexivity | exact (proj1 (used_metas_iff s h ah ND) Hu)]).
    destruct (ufacts h ah Uh) as (Sh & Lh & Oh).
    exists (slot_end ah (am_last ah)). split; [reflexivity|]. unfold gend_cell. cbn [mc_w Z.of_nat Pos.of_succ_nat].
    unfold slot_end. rewrite prid_padd, poff_padd, prid_slot_start. pose proof (st_last ah) as EL.
    destruct (Nat.eq_dec (prid (am_mem ah)) (prid (am_mem aq))) as [Erc|Erc]; [|left; exact Erc]. right.
    pose proof (ext28 h ah Uh) as Xh. pose proof (ext28 q aq Uq) as Xq'.
    destruct (sptr_eq_dec h q) as [<-|Hhq].
    + pose proof (usedX_fun _ _ _ _ _ Uq Uh) as ->. right. unfold IB in *. lia.
    + destruct (inv_laminar HI h ah q aq Uh Uq Hhq Erc) as [D | [I | I]].
      * unfold spans_disjoint in D. destruct D as [D|D]; [|right; unfold IB in *; lia].
        destruct (Z.eq_dec (poff (am_mem ah) + group_extent ah) (poff (am_mem aq))) as [E|E].
        -- exfalso. exact (adjacency_impossible h ah q aq Uh Uq Hhq Erc E).
        -- left. unfold IB in *. lia.
      * destruct (inside_slot_start [] R U s HI h ah (am_last ah) q aq Uh Uq ltac:(lia) I) as (k & fr' & Hk & _ & _ & A & B).
        pose proof (slot_in_span [] R U s HI q aq k Uq Hk) as [SK1 _]. right. unfold UNIT, IB in *. lia.
      * destruct (inside_slot_start [] R U s HI q aq 0 h ah Uq Uh ltac:(lia) I) as (k & fr' & Hk & _ & _ & A & B).
        pose proof (poff_slot_start aq 0) as E0. rewrite Z.mul_0_r in E0.
        destruct (Z.eq_dec k (am_last ah)) as [->|Hkj]; [right; unfold UNIT, IB in *; lia|].
        destruct (same_group_starts ah k (am_last ah) Hkj Sh); unfold UNIT, IB in *; lia.
Qed.

(* [comment removed for export] *)
#[using="R U HI"] Lemma marker_region : forall c, In c (markers s) ->
  exists qc rg, mc_loc c = LMem qc /\ region_of s (prid qc) = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
    0 <= poff qc /\ poff qc + Z.of_nat (mc_w c) <= rg_len rg.
Proof. LiaFast.lf_pins (fun (R U HI : LiaFast.U) => LiaFast.u0).
  intros c Hc. assert (ND : List.NoDup (keys s)) by exact (proj1 (inv_keys HI)).
  destruct (In_markers_inv s c Hc) as [(h & ah & j & fr & HF & Kfr & Hc') | (h & ah & Hu & ->)].
  - destruct (in_frames_inv s h ah j fr HF) as (Hu & Hj & Hfr).
    assert (Uh : usedX [] s h ah) by (apply usedX_intro; [reflexivity | exact (proj1 (used_metas_iff s h ah ND) Hu)]).
    pose proof (inv_groups HI h ah Uh) as (_ & _ & Gsl & _). pose proof (Gsl j Hj) as (_ & _ & S3). rewrite Hfr in S3.
    destruct S3 as (_ & _ & (N0 & O0 & F0 & _) & _).
    destruct (marker_cells_span ah j fr c ltac:(lia) N0 F0 Hc') as (qc & Eq & Hq1 & Hq2 & Hq3).
    destruct (used_group_region [] R U s h ah HI Uh) as (rg & Hr & Hk & Hl & Ho & Hext & _).
    pose proof (slot_in_span [] R U s HI h ah j Uh Hj) as [SJ1 SJ2].
    exists qc, rg. rewrite Hq1, prid_slot_start. split; [exact Eq|]. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hl|].
    unfold UNIT, IB in *. lia.
  - assert (Uh : usedX [] s h ah) by (apply usedX_intro; [reflexivity | exact (proj1 (used_metas_iff s h ah ND) Hu)]).
    destruct (ufacts h ah Uh) as (Sh & Lh & Oh).
    destruct (used_group_region [] R U s h ah HI Uh) as (rg & Hr & Hk & Hl & Ho & Hext & _).
    pose proof (st_last ah) as EL.
    exists (slot_end ah (am_last ah)), rg. unfold gend_cell, slot_end. rewrite prid_padd, poff_padd, prid_slot_start.
    split; [reflexivity|]. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hl|]. cbn [mc_w Z.of_nat Pos.of_succ_nat].
    pose proof (ext28 h ah Uh). unfold IB in *. lia.
Qed.

#[using="Type"] Lemma slot_cells_narrow : forall am i c, In c (slot_cells am i) -> (mc_w c <= 2)%nat.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros am i c Hin. unfold slot_cells in Hin. apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]].
  - destruct Hin as [<-|[]]. cbn. lia.
  - destruct (ss_hdr (nth_slot am i)) as [[h3 h16]|]; [|destruct Hin]. destruct Hin as [<-|[<-|[]]]; cbn; lia.
  - destruct (ss_fr (nth_slot am i)) as [fr|]; [|destruct Hin]. destruct (fr_off fr =? 0); [destruct Hin|].
    destruct Hin as [<-|[<-|[<-|[]]]]; cbn; lia.
Qed.

#[using="Type"] Lemma loc_SP : forall L r o, loc_addr L (LMem (SP r o)) = ly_reg L r + o.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

(* [comment removed for export] *)
#[using="R U HI"] Theorem markers_vs_wide : forall L c c', layout_ok L s -> ly_ctx L = 0x97c98 ->
  (forall rg, In rg (footprint s) -> fst rg <> LCtx 0 -> ranges_disjoint (crange L rg) (0x10000, 0x89000)) ->
  In c (markers s) -> In c' (image s) -> ((0x97c98 <= loc_addr L (mc_loc c') < 0x98038) \/ (4 <= mc_w c')%nat) ->
  ranges_disjoint (cell_range L c) (cell_range L c').
Proof. LiaFast.lf_pins (fun (R U HI : LiaFast.U) => LiaFast.u0).
  intros L c c' HL Hctx HAP Hc Hc' Hw.
  assert (ND : List.NoDup (keys s)) by exact (proj1 (inv_keys HI)).
  pose proof HL as (_ & _ & Ldisj & _).
  destruct (marker_region c Hc) as (qc & rgc & Ec & Hrc & Kc & Lvc & Oc & Wc).
  assert (FC : In (LMem (SP (prid qc) 0), rg_len rgc) (footprint s)) by (apply footprint_region_In; assumption).
  assert (INC : range_incl (cell_range L c) (crange L (LMem (SP (prid qc) 0), rg_len rgc))).
  { unfold range_incl, cell_range, crange. cbn [fst snd]. rewrite Ec. destruct qc as [rq oq]. rewrite !loc_SP. cbn [prid poff] in *. lia. }
  pose proof (HAP _ FC ltac:(discriminate)) as DFC.
  unfold range_incl, ranges_disjoint, crange, cell_range in *. cbn [fst snd] in *. rewrite Ec in INC |- *.
  rewrite image_parts in Hc'. apply in_app_iff in Hc' as [Hc'|Hc']; [|apply in_app_iff in Hc' as [Hc'|Hc']].
  - (* [comment removed for export] *)
    destruct (In_ctx_cells s c' Hc') as (o & Eo & Ho1 & Ho2). rewrite Eo in *. cbn [loc_addr] in *. rewrite Hctx in *. unfold CTX_SIZE in *. lia.
  - (* [comment removed for export] *)
    destruct (In_areas_cells s (st_areas s) c' Hc') as (a & next & Ha & Hc2). destruct (In_area_cells s a next c' Hc2) as (d & Ed & Hd1 & Hd2).
    pose proof (area_page_In s a Ha) as FA.
    pose proof (inv_areas HI) as (_ & AOK & _). destruct (AOK a Ha) as (ra & oa & rga & Ea & _ & _ & Hra & _ & _ & Hkind).
    assert (Hne : (LMem a, PGSZ) <> (LMem (SP (prid qc) 0), rg_len rgc)).
    { intros E. injection E as E1 _. rewrite Ea in E1. injection E1 as E2 _. subst ra. rewrite Hrc in Hra. injection Hra as <-. rewrite Kc in Hkind. exact Hkind. }
    destruct (pairwise_map_In _ (crange L) _ _ _ Ldisj FA FC Hne) as [D|D]; unfold ranges_disjoint, crange in D; cbn [fst snd] in D;
      rewrite Ed, loc_padd in *; unfold PGSZ in *; lia.
  - (* [comment removed for export] *)
    unfold gpart in Hc'. apply in_flat_map in Hc' as [[q aq] [Hq Hc2]]. cbn [fst snd] in Hc2.
    assert (Mq : MT s q = Some (MUsed aq)) by exact (proj1 (used_metas_iff s q aq ND) Hq).
    assert (Uq : usedX [] s q aq) by (apply usedX_intro; [reflexivity | exact Mq]).
    destruct (used_group_region [] R U s q aq HI Uq) as (rgq & Hrq & Hkq & Hlq & Hoq & Hextq & _).
    pose proof (ext28 q aq Uq) as X28.
    assert (FQ : In (LMem (SP (prid (am_mem aq)) 0), rg_len rgq) (footprint s)) by (apply footprint_region_In; assumption).
    unfold group_cells in Hc2. apply in_app_iff in Hc2 as [Hc2|Hc2].
    + (* [comment removed for export] *)
      assert (HH : exists d, mc_loc c' = LMem (padd (am_mem aq) d) /\ 0 <= d /\ d + Z.of_nat (mc_w c') <= 12).
      { destruct Hc2 as [<-|[<-|[]]]; [exists 0; rewrite padd_0; split; [reflexivity | cbn; lia]|].
        destruct (am_maplen aq =? 0); [exists 8; split; [reflexivity | cbn; lia] | exists 8; split; [reflexivity | cbn; lia]]. }
      destruct HH as (d & Ed & Hd1 & Hd2). rewrite Ed, loc_padd in *.
      destruct (markers_vs_hdr c q aq Hc Mq) as (qc' & Ec' & [Hdr|[Hdr|Hdr]]); rewrite Ec in Ec'; injection Ec' as <-.
      * assert (Hne : (LMem (SP (prid (am_mem aq)) 0), rg_len rgq) <> (LMem (SP (prid qc) 0), rg_len rgc)).
        { intros E. injection E as E1 _. exact (Hdr (eq_sym E1)). }
        destruct (pairwise_map_In _ (crange L) _ _ _ Ldisj FQ FC Hne) as [D|D]; unfold ranges_disjoint, crange in D; cbn [fst snd] in D;
          destruct (am_mem aq) as [rm om]; cbn [prid poff] in *; rewrite ?loc_SP in *; unfold IB in *; lia.
      * destruct qc as [rq oq]. destruct (am_mem aq) as [rm om]. cbn [prid poff] in *. rewrite !loc_SP in *.
        destruct (Nat.eq_dec rq rm) as [->|Hrr].
        -- lia.
        -- assert (Hne : (LMem (SP rm 0), rg_len rgq) <> (LMem (SP rq 0), rg_len rgc)) by (intros E; injection E as E1 _; congruence).
           destruct (pairwise_map_In _ (crange L) _ _ _ Ldisj FQ FC Hne) as [D|D]; unfold ranges_disjoint, crange in D; cbn [fst snd] in D;
             rewrite ?loc_SP in *; unfold IB in *; lia.
      * destruct qc as [rq oq]. destruct (am_mem aq) as [rm om]. cbn [prid poff] in *. rewrite !loc_SP in *.
        destruct (Nat.eq_dec rq rm) as [->|Hrr].
        -- lia.
        -- assert (Hne : (LMem (SP rm 0), rg_len rgq) <> (LMem (SP rq 0), rg_len rgc)) by (intros E; injection E as E1 _; congruence).
           destruct (pairwise_map_In _ (crange L) _ _ _ Ldisj FQ FC Hne) as [D|D]; unfold ranges_disjoint, crange in D; cbn [fst snd] in D;
             rewrite ?loc_SP in *; unfold IB in *; lia.
    + (* [comment removed for export] *)
      apply in_flat_map in Hc2 as [j [Hj Hc3]]. apply In_zseq in Hj.
      pose proof (slot_cells_narrow aq j c' Hc3) as NW.
      destruct (In_slot_cells [] R U s q aq j c' HI Uq ltac:(lia) Hc3) as (d & Ed & Hd1 & Hd2 & _).
      exfalso. destruct Hw as [Hw|Hw]; [|lia].
      pose proof (HAP _ FQ ltac:(discriminate)) as DFQ. unfold ranges_disjoint, crange in DFQ. cbn [fst snd] in DFQ.
      pose proof (slot_in_span [] R U s HI q aq j Uq ltac:(lia)) as [SJ1 SJ2]. rewrite poff_slot_start in SJ1, SJ2.
      rewrite Ed, loc_padd in Hw. destruct (am_mem aq) as [rm om]. cbn [prid poff] in *. rewrite !loc_SP in *.
      pose proof (image_cell_width s c' ltac:(rewrite image_parts; apply in_app_iff; right; apply in_app_iff; right;
        unfold gpart; apply in_flat_map; exists (q, aq); split; [exact Hq | cbn [fst snd]; unfold group_cells; apply in_app_iff; right; apply in_flat_map;
        exists j; split; [apply In_zseq; lia | exact Hc3]])) as W1.
      destruct (ufacts q aq Uq) as (Sq & _ & _). assert (0 <= stride_of aq * j) by (apply Z.mul_nonneg_nonneg; lia).
      unfold UNIT, IB in *. lia.
Qed.
End G.
