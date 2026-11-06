(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition free_slot_range (L : layout) (am : ameta) (k : Z) : Z * Z :=
  (loc_addr L (LMem (slot_start am k)) - 3, stride_of am - 1).

Theorem image_outside_free_slot : forall s L c g am k,
  WF s -> layout_ok L s -> usedX [] s g am -> 0 <= k <= am_last am -> ss_fr (nth_slot am k) = None ->
  In c (image s) -> ~ In c (slot_cells am k) ->
  ranges_disjoint (cell_range L c) (free_slot_range L am k).
Proof.
  intros s L c g am k HW HL Hg Hk Hfr Hc Hnk. pose proof HL as (_ & _ & PW & _).
  pose proof (inv_groups HW g am Hg) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp. pose proof G as (_ & _ & Gsl & _).
  destruct (used_group_region [] None U0 s g am HW Hg) as (rg & Hr & Hkd & Hl & Ho & Hext & _).
  pose proof (footprint_region_In s _ _ Hr Hkd Hl) as InR.
  pose proof (slot_in_span [] None U0 s HW g am k Hg Hk) as [S1 S1'].
  assert (BI : range_incl (free_slot_range L am k) (crange L (LMem (SP (prid (am_mem am)) 0), rg_len rg))).
  { unfold free_slot_range, crange, range_incl, loc_addr. cbn [fst snd].
    unfold slot_start in *. destruct (am_mem am) as [r o]. cbn [padd prid poff] in *. unfold group_extent, IB, UNIT in *. lia. }
  assert (VIA : forall e, In e (footprint s) -> e <> (LMem (SP (prid (am_mem am)) 0), rg_len rg) ->
            range_incl (cell_range L c) (crange L e) -> ranges_disjoint (cell_range L c) (free_slot_range L am k)).
  { intros e He Hne Hincl.
    destruct (pairwise_map_In ranges_disjoint (crange L) (footprint s) _ _ PW He InR Hne) as [D|D].
    - eapply ranges_disjoint_incl; [exact D | exact Hincl | exact BI].
    - apply ranges_disjoint_sym. eapply ranges_disjoint_incl; [exact D | exact BI | exact Hincl]. }
  destruct (In_image_inv s c Hc) as [Hcc | [(a & next & Ha & Hcc) | (g' & am' & Hg' & Hcc)]].
  - destruct (In_ctx_cells s c Hcc) as (off & E & Ho' & Hw). apply (VIA (LCtx 0, CTX_SIZE)); [left; reflexivity | discriminate |].
    unfold cell_range, crange, range_incl, loc_addr. rewrite E. cbn [fst snd]. lia.
  - destruct (In_area_cells s a next c Hcc) as (d & E & Hd & Hw).
    pose proof (inv_areas HW) as (_ & A2 & _). destruct (A2 a Ha) as (ra & oa & rga & Ea & _ & Hoa & _).
    apply (VIA (LMem a, PGSZ)).
    + right. apply in_app_iff. left. apply in_map_iff. exists a. auto.
    + rewrite Ea. intros E2. injection E2 as _ Eo _. unfold PGSZ in Hoa. lia.
    + unfold cell_range, crange, range_incl, loc_addr. rewrite E. destruct a as [r o]. cbn [fst snd padd]. lia.
  - apply (used_metas_usedX s g' am' HW) in Hg'.
    destruct (Nat.eq_dec (prid (am_mem am')) (prid (am_mem am))) as [Hsame | Hdiff].
    2:{ destruct (used_group_region [] None U0 s g' am' HW Hg') as (rg' & Hr' & Hkd' & Hl' & Ho2 & Hext' & _).
        destruct (In_group_cells_span [] None U0 s g' am' c HW Hg' Hcc) as (d & E & Hd & Hw).
        apply (VIA (LMem (SP (prid (am_mem am')) 0), rg_len rg')); [apply footprint_region_In; assumption | intros E2; injection E2; intros _ Ep; exact (Hdiff Ep) |].
        unfold cell_range, crange, range_incl, loc_addr. rewrite E. destruct (am_mem am') as [r o]. cbn [fst snd padd prid poff] in *. unfold IB in *. lia. }
    (* [comment removed for export] *)
    assert (GOAL : forall d, mc_loc c = LMem (padd (am_mem am') d) ->
              (poff (am_mem am') + d + Z.of_nat (mc_w c) <= poff (slot_start am k) - 3 \/
               poff (slot_start am k) + stride_of am - 5 < poff (am_mem am') + d) ->
              ranges_disjoint (cell_range L c) (free_slot_range L am k)).
    { intros d E D. unfold cell_range, free_slot_range, ranges_disjoint, loc_addr. rewrite E. cbn [fst snd].
      unfold slot_start in *. destruct (am_mem am') as [r' o'], (am_mem am) as [r o]. cbn [padd prid poff] in *. subst r'. lia. }
    destruct (sptr_eq_dec g' g) as [->|Hne].
    + pose proof (usedX_fun _ _ _ _ _ Hg' Hg) as ->.
      unfold group_cells in Hcc. apply in_app_iff in Hcc as [Hcc|Hcc].
      * destruct Hcc as [<-|[<-|[]]].
        -- apply (GOAL 0); [cbn; rewrite padd_0; reflexivity|]. left. rewrite poff_slot_start. cbn [mc_w Z.of_nat Pos.of_succ_nat]. unfold UNIT in *. nia.
        -- destruct (am_maplen am =? 0); (apply (GOAL 8); [reflexivity|]); left; rewrite poff_slot_start; cbn [mc_w Z.of_nat Pos.of_succ_nat]; unfold UNIT in *; nia.
      * apply in_flat_map in Hcc as [j [Hj Hcj]]. apply In_zseq in Hj.
        destruct (Z.eq_dec j k) as [->|Hjk]; [contradiction|].
        destruct (In_slot_cells [] None U0 s g am j c HW Hg ltac:(lia) Hcj) as (d & E & Lo & Hiw & _).
        apply (GOAL d E). rewrite poff_slot_start.
        assert (j < k \/ k < j) as [Hlt|Hlt] by lia; [left|right];
          [assert (stride_of am * j + stride_of am <= stride_of am * k) by nia | assert (stride_of am * k + stride_of am <= stride_of am * j) by nia];
          unfold UNIT, IB in *; lia.
    + pose proof (extent_pos _ _ _ _ _ (inv_groups HW g' am' Hg')) as Pa'.
      destruct (inv_laminar HW g' am' g am Hg' Hg Hne Hsame) as [Dj | [I | I]].
      * destruct (In_group_cells_span [] None U0 s g' am' c HW Hg' Hcc) as (d & E & Hd & Hw). apply (GOAL d E).
        unfold spans_disjoint in Dj. rewrite poff_slot_start. rewrite poff_slot_start in S1, S1'.
        unfold UNIT, IB in *. destruct Dj; [left|right]; lia.
      * (* [comment removed for export] *)
        destruct (In_group_cells_span [] None U0 s g' am' c HW Hg' Hcc) as (d & E & Hd & Hw). apply (GOAL d E).
        destruct I as (j0 & fr0 & c0 & ac0 & Hj0 & Hfr0 & Hk0 & Uc0 & Ml0 & Mem0 & Lo0 & Hi0 & Fit0).
        destruct (Z.eq_dec j0 k) as [->|Hji]; [rewrite Hfr in Hfr0; discriminate|].
        pose proof (Gsl j0 Hj0) as (_ & _ & S3). rewrite Hfr0 in S3. destruct S3 as (_ & _ & (N0 & O0 & B0 & _) & _).
        rewrite Mem0, poff_slot_start in Lo0, Hi0.
        destruct (same_group_starts am j0 k Hji Sp) as [LE|LE]; rewrite !poff_slot_start in *; unfold group_extent, UNIT, IB in *; [left|right]; lia.
      * (* [comment removed for export] *)
        destruct I as (j' & fr' & c0 & ac0 & Hj' & Hfr' & Hk' & Uc0 & Ml0 & Mem0 & Lo0 & Hi0 & Fit0).
        pose proof (inv_groups HW g' am' Hg') as (_ & _ & Gsl' & _). pose proof (Gsl' j' Hj') as (_ & _ & S3'). rewrite Hfr' in S3'.
        destruct S3' as (_ & _ & (N' & O' & B' & _ & FG') & _). destruct (FG' Hk') as [Off' Fn'].
        destruct (group_cells_vs_body [] None U0 s g' am' j' (poff (slot_start am k) - 3) (poff (slot_start am k) + stride_of am - 4) c HW Hg' Hj' Hcc) as (d & E & D).
        -- rewrite Hfr', Off'. rewrite Mem0 in Lo0. rewrite !poff_slot_start in *. unfold UNIT, IB in *. lia.
        -- rewrite Mem0 in Hi0. rewrite !poff_slot_start in *. unfold group_extent, UNIT, IB in *. lia.
        -- apply (GOAL d E). lia.
Qed.


(* [comment removed for export] *)
Lemma marker_cells_span' : forall am i fr c, 0 <= fr_off fr -> 0 <= fr_n fr -> UNIT * fr_off fr + fr_n fr <= stride_of am - IB ->
  In c (marker_cells am i fr) ->
  exists q, mc_loc c = LMem q /\ prid q = prid (slot_start am i) /\
    poff (slot_start am i) + UNIT * fr_off fr + fr_n fr <= poff q /\ poff q + Z.of_nat (mc_w c) <= poff (slot_start am i) + stride_of am - IB + 1.
Proof.
  intros am i fr c H0 H1 H2 Hc. unfold marker_cells, slot_end, frame_rsv in Hc. unfold UNIT, IB in *.
  destruct Hc as [<-|Hc].
  - exists (padd (slot_start am i) (stride_of am - 4)). cbn [mc_loc mc_w]. rewrite prid_padd, poff_padd. repeat split; lia.
  - apply in_app_iff in Hc as [Hc|Hc].
    + destruct (0 <? stride_of am - 4 - 16 * fr_off fr - fr_n fr) eqn:E; [|destruct Hc]. apply Z.ltb_lt in E.
      destruct Hc as [<-|[]]. exists (padd (padd (slot_start am i) (stride_of am - 4)) (- (stride_of am - 4 - 16 * fr_off fr - fr_n fr))).
      cbn [mc_loc mc_w]. rewrite !prid_padd, !poff_padd. repeat split; lia.
    + destruct (5 <=? stride_of am - 4 - 16 * fr_off fr - fr_n fr) eqn:E; [|destruct Hc]. apply Z.leb_le in E.
      destruct Hc as [<-|[<-|[]]];
        [exists (padd (padd (slot_start am i) (stride_of am - 4)) (-4)) | exists (padd (padd (slot_start am i) (stride_of am - 4)) (-5))];
        cbn [mc_loc mc_w]; rewrite !prid_padd, !poff_padd; repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma markers_span : forall s g2 a2 c, WF s -> usedX [] s g2 a2 -> In c (meta_markers a2) ->
  exists q, mc_loc c = LMem q /\ prid q = prid (am_mem a2) /\ poff (am_mem a2) + UNIT <= poff q /\
    poff q + Z.of_nat (mc_w c) <= poff (am_mem a2) + group_extent a2 + 1 /\
    ((exists i fr, 0 <= i <= am_last a2 /\ ss_fr (nth_slot a2 i) = Some fr /\ fr_kind fr = FUser /\
        poff (slot_start a2 i) <= poff q /\ poff q + Z.of_nat (mc_w c) <= poff (slot_start a2 i) + stride_of a2 - IB + 1)
     \/ c = gend_cell a2).
Proof.
  intros s g2 a2 c HW Hu Hc. pose proof (inv_groups HW g2 a2 Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
  pose proof G as ((Mlast & _) & _ & Gsl & _).
  unfold meta_markers in Hc. apply in_app_iff in Hc as [Hc|[Hc|[]]].
  - apply in_flat_map in Hc as [i [Hi Hc]]. apply In_zseq in Hi.
    destruct (ss_fr (nth_slot a2 i)) as [fr|] eqn:Efr; [|destruct Hc]. destruct (fr_kind fr) eqn:Ek; [|destruct Hc].
    pose proof (Gsl i ltac:(lia)) as (_ & _ & S3). rewrite Efr in S3. destruct S3 as (_ & _ & (N & O & B & _) & _).
    destruct (marker_cells_span' a2 i fr c ltac:(lia) N B Hc) as (q & E & Pq & Lo & Hi2). exists q. split; [exact E|].
    rewrite prid_slot_start in Pq. split; [exact Pq|].
    rewrite poff_slot_start in *.
    assert (0 <= stride_of a2 * i) by nia. assert (stride_of a2 * i + stride_of a2 <= stride_of a2 * (am_last a2 + 1)) by nia.
    unfold group_extent, UNIT, IB in *. split; [lia|]. split; [lia|].
    left. exists i, fr. split; [lia|]. split; [exact Efr|]. split; [exact Ek|]. rewrite !poff_slot_start. unfold UNIT, IB. lia.
  - subst c. exists (slot_end a2 (am_last a2)). split; [reflexivity|]. unfold slot_end. rewrite prid_padd, prid_slot_start. split; [reflexivity|].
    rewrite poff_padd, poff_slot_start. cbn [mc_w Z.of_nat Pos.of_succ_nat].
    assert (0 <= stride_of a2 * am_last a2) by (apply Z.mul_nonneg_nonneg; lia).
    assert (E1 : stride_of a2 * (am_last a2 + 1) = stride_of a2 * am_last a2 + stride_of a2) by ring.
    unfold group_extent, UNIT, IB in *. rewrite E1. split; [lia|]. split; [cbn [gend_cell mc_w Z.of_nat Pos.of_succ_nat]; lia|].
    right. reflexivity.
Qed.

Theorem markers_outside_free_slot : forall s L c g am k,
  WF s -> layout_ok L s -> usedX [] s g am -> 0 <= k <= am_last am -> ss_fr (nth_slot am k) = None ->
  In c (markers s) ->
  ranges_disjoint (cell_range L c) (free_slot_range L am k).
Proof.
  intros s L c g am k HW HL Hg Hk Hfr Hc. pose proof HL as (_ & _ & PW & _).
  pose proof (inv_groups HW g am Hg) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp. pose proof G as (_ & _ & Gsl & _).
  destruct (used_group_region [] None U0 s g am HW Hg) as (rg & Hr & Hkd & Hl & Ho & Hext & _).
  pose proof (footprint_region_In s _ _ Hr Hkd Hl) as InR.
  pose proof (slot_in_span [] None U0 s HW g am k Hg Hk) as [S1 S1'].
  unfold markers in Hc. apply in_flat_map in Hc as [[g2 a2] [Hu2 Hc]]. cbn [snd] in Hc.
  apply (used_metas_usedX s g2 a2 HW) in Hu2.
  destruct (markers_span s g2 a2 c HW Hu2 Hc) as (q & Eq & Pq & Lo & Hi & Fine).
  destruct (used_group_region [] None U0 s g2 a2 HW Hu2) as (rg2 & Hr2 & Hkd2 & Hl2 & Ho2 & Hext2 & _).
  assert (GOAL : poff q + Z.of_nat (mc_w c) <= poff (slot_start am k) - 3 \/ poff (slot_start am k) + stride_of am - 5 < poff q ->
                 prid q = prid (am_mem am) -> ranges_disjoint (cell_range L c) (free_slot_range L am k)).
  { intros D Ep. clear Pq Lo Hi Fine. unfold cell_range, free_slot_range, ranges_disjoint, loc_addr. rewrite Eq. cbn [fst snd].
    unfold slot_start in *. destruct q as [r2 o2], (am_mem am) as [r o]. cbn [padd prid poff] in *. subst r2. lia. }
  destruct (Nat.eq_dec (prid (am_mem a2)) (prid (am_mem am))) as [Hsame | Hdiff].
  2:{ (* [comment removed for export] *)
      assert (F2 : In (LMem (SP (prid (am_mem a2)) 0), rg_len rg2) (footprint s)) by (apply footprint_region_In; assumption).
      assert (Hne : (LMem (SP (prid (am_mem a2)) 0), rg_len rg2) <> (LMem (SP (prid (am_mem am)) 0), rg_len rg)) by (intros E; injection E; intros _ E2; exact (Hdiff E2)).
      destruct (pairwise_map_In ranges_disjoint (crange L) (footprint s) _ _ PW F2 InR Hne) as [D|D];
        unfold crange, ranges_disjoint, cell_range, free_slot_range, loc_addr in *; rewrite Eq in *; cbn [fst snd] in *;
        unfold slot_start, group_extent, UNIT, IB in *; destruct q as [r2 o2], (am_mem a2) as [ra oa], (am_mem am) as [r o];
        cbn [padd prid poff] in *; subst; lia. }
  apply GOAL; [|rewrite Pq; exact Hsame].
  rewrite poff_slot_start in *.
  destruct (sptr_eq_dec g2 g) as [->|Hne].
  - pose proof (usedX_fun _ _ _ _ _ Hu2 Hg) as ->.
    destruct Fine as [(i & fr & Hi2 & Efr & Ek & A & B) | ->].
    + destruct (Z.eq_dec i k) as [->|Hik]; [rewrite Hfr in Efr; discriminate|].
      rewrite poff_slot_start in A, B.
      assert (i < k \/ k < i) as [Lt|Lt] by lia; [left|right];
        [assert (stride_of am * i + stride_of am <= stride_of am * k) by nia | assert (stride_of am * k + stride_of am <= stride_of am * i) by nia];
        unfold UNIT, IB in *; lia.
    + right. cbn [gend_cell mc_loc] in Eq. injection Eq as <-. unfold slot_end. rewrite poff_padd, poff_slot_start.
      assert (stride_of am * k <= stride_of am * am_last am) by nia. unfold UNIT, IB in *. lia.
  - pose proof (extent_pos _ _ _ _ _ (inv_groups HW g2 a2 Hu2)) as Pa2.
    destruct (inv_laminar HW g2 a2 g am Hu2 Hg Hne Hsame) as [Dj | [I | I]].
    + unfold spans_disjoint in Dj. unfold group_extent, UNIT, IB in *. destruct Dj; [left|right]; lia.
    + (* [comment removed for export] *)
      destruct I as (j0 & fr0 & c0 & ac0 & Hj0 & Hfr0 & Hk0 & Uc0 & Ml0 & Mem0 & Lo0 & Hi0 & Fit0).
      destruct (Z.eq_dec j0 k) as [->|Hji]; [rewrite Hfr in Hfr0; discriminate|].
      pose proof (Gsl j0 Hj0) as (_ & _ & S3). rewrite Hfr0 in S3. destruct S3 as (_ & _ & (N0 & O0 & B0 & _) & _).
      rewrite Mem0 in Lo0, Hi0. rewrite !poff_slot_start in Lo0, Hi0.
      assert (j0 < k \/ k < j0) as [Lt|Lt] by lia; [left|right];
        [assert (stride_of am * j0 + stride_of am <= stride_of am * k) by nia | assert (stride_of am * k + stride_of am <= stride_of am * j0) by nia];
        unfold group_extent, UNIT, IB in *; lia.
    + (* [comment removed for export] *)
      destruct I as (j' & fr' & c0 & ac0 & Hj' & Hfr' & Hk' & Uc0 & Ml0 & Mem0 & Lo0 & Hi0 & Fit0).
      pose proof (inv_groups HW g2 a2 Hu2) as G2. pose proof (stride_pos _ _ _ _ _ G2) as Sp2. pose proof G2 as (_ & _ & Gsl2 & _).
      pose proof (Gsl2 j' Hj') as (_ & _ & S3'). rewrite Hfr' in S3'.
      destruct S3' as (_ & _ & (N' & O' & B' & _ & FG') & _). destruct (FG' Hk') as [Off' Fn'].
      rewrite Mem0 in Lo0, Hi0. rewrite !poff_slot_start in Lo0, Hi0.
      destruct Fine as [(i & fr & Hi2 & Efr & Ek & A & B) | ->].
      * destruct (Z.eq_dec i j') as [->|Hij]; [rewrite Efr in Hfr'; injection Hfr' as <-; rewrite Ek in Hk'; discriminate|].
        rewrite !poff_slot_start in A, B.
        assert (i < j' \/ j' < i) as [Lt|Lt] by lia; [left|right];
          [assert (stride_of a2 * i + stride_of a2 <= stride_of a2 * j') by nia | assert (stride_of a2 * j' + stride_of a2 <= stride_of a2 * i) by nia];
          unfold group_extent, UNIT, IB in *; lia.
      * right. cbn [gend_cell mc_loc] in Eq. injection Eq as <-. unfold slot_end. rewrite poff_padd, poff_slot_start.
        pose proof G2 as ((Ml2 & _) & _).
        assert (stride_of a2 * j' <= stride_of a2 * am_last a2) by nia. unfold group_extent, UNIT, IB in *. lia.
Qed.
