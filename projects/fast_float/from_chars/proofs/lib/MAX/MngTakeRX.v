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
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngGeoX MngTake MngOwn MngTakeR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma markers_span_X : forall X R U s (HXU : XNU X s) g2 a2 c, Inv X R U s -> usedX X s g2 a2 -> In c (meta_markers a2) ->
  exists q, mc_loc c = LMem q /\ prid q = prid (am_mem a2) /\ poff (am_mem a2) + UNIT <= poff q /\
    poff q + Z.of_nat (mc_w c) <= poff (am_mem a2) + group_extent a2 + 1 /\
    ((exists i fr, 0 <= i <= am_last a2 /\ ss_fr (nth_slot a2 i) = Some fr /\ fr_kind fr = FUser /\
        poff (slot_start a2 i) <= poff q /\ poff q + Z.of_nat (mc_w c) <= poff (slot_start a2 i) + stride_of a2 - IB + 1)
     \/ c = gend_cell a2).
Proof.
  intros X R U s HXU g2 a2 c HW Hu Hc. pose proof (inv_groups HW g2 a2 Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
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

Theorem markers_outside_free_slot_X : forall X R U s L c g am k,
  Inv X R U s -> XNU X s -> layout_ok L s -> usedX X s g am -> 0 <= k <= am_last am -> ss_fr (nth_slot am k) = None ->
  In c (markers s) ->
  ranges_disjoint (cell_range L c) (free_slot_range L am k).
Proof.
  intros X R U s L c g am k HW HXU HL Hg Hk Hfr Hc. pose proof HL as (_ & _ & PW & _).
  pose proof (inv_groups HW g am Hg) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp. pose proof G as (_ & _ & Gsl & _).
  destruct (used_group_region X R U s g am HW Hg) as (rg & Hr & Hkd & Hl & Ho & Hext & _).
  pose proof (footprint_region_In s _ _ Hr Hkd Hl) as InR.
  pose proof (slot_in_span X R U s HW g am k Hg Hk) as [S1 S1'].
  unfold markers in Hc. apply in_flat_map in Hc as [[g2 a2] [Hu2 Hc]]. cbn [snd] in Hc.
  apply (used_metas_usedX_X X R U s g2 a2 HW HXU) in Hu2.
  destruct (markers_span_X X R U s HXU g2 a2 c HW Hu2 Hc) as (q & Eq & Pq & Lo & Hi & Fine).
  destruct (used_group_region X R U s g2 a2 HW Hu2) as (rg2 & Hr2 & Hkd2 & Hl2 & Ho2 & Hext2 & _).
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

Lemma marker_in_region_X : forall X R U s (L : layout) c, Inv X R U s -> XNU X s -> In c (markers s) ->
  exists r rg o, region_of s r = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\ mc_loc c = LMem (SP r o) /\
    0 <= o /\ o + Z.of_nat (mc_w c) <= rg_len rg.
Proof.
  intros X R U s L c HW HXU Hc. unfold markers in Hc. apply in_flat_map in Hc as [[g2 a2] [Hu2 Hc]]. cbn [snd] in Hc.
  apply (used_metas_usedX_X X R U s g2 a2 HW HXU) in Hu2.
  destruct (markers_span_X X R U s HXU g2 a2 c HW Hu2 Hc) as (q & Eq & Pq & Lo & Hi & _).
  destruct (used_group_region X R U s g2 a2 HW Hu2) as (rg & Hr & Hkd & Hl & Ho & Hext & _).
  destruct q as [r o]. cbn [prid poff] in *. exists r, rg, o. subst r. split; [exact Hr|]. split; [exact Hkd|]. split; [exact Hl|].
  split; [exact Eq|]. unfold group_extent, UNIT, IB in *. split; lia.
Qed.
