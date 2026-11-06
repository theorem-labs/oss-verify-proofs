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
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng MngRepr MngHeap MngImage MngSurgery MngCtx MngTake MngMalloc.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_efz.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRepr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngImage OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngSurgery OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngCtx OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngTake OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMalloc OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efz.AXF_efa1z.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Lemma repr_from_pre : forall L s s' (bv bv' : byteview) (Cnew : list mcell),
  repr L s bv -> layout_ok L s' -> Forall (range_mapped L bv') (footprint s') ->
  (forall c, In c (image s') -> In c (image s) \/ In c Cnew) ->
  Forall (cell_holds L bv') Cnew ->
  (forall c a, In c (image s') -> In c (image s) -> ~ In c Cnew -> in_rng (cell_range L c) a -> bv' a = bv a) ->
  (forall c, In c (image s') -> (1 <= mc_w c)%nat) ->
  repr L s' bv'.
Proof.
  intros L s s' bv bv' Cnew (HL & HC & HF) HL' HF' Hcov HNew HUN HWd.
  split; [exact HL'|]. split; [|exact HF'].
  apply Forall_forall. intros c Hc. destruct (In_dec mcell_eq_dec c Cnew) as [Hn|Hn].
  - exact (proj1 (Forall_forall _ _) HNew c Hn).
  - destruct (Hcov c Hc) as [H1|H1]; [|contradiction].
    apply (cell_holds_frame L bv bv' c (HWd c Hc) (proj1 (Forall_forall _ _) HC c H1)).
    intros a Ha. exact (HUN c a Hc H1 Hn Ha).
Qed.

Definition mf_am2 (am : ameta) (n off0 : Z) : ameta := ef_am (mf_am1 am) (mf_idx am) n (ef_offm am n off0).
Definition mf_hdr (am : ameta) (n off0 : Z) : Z * Z := ef_hdrm (mf_am1 am) (mf_idx am) n (ef_offm am n off0).
Definition mf_fr (am : ameta) (n off0 : Z) : frame := mkFrame (ef_offm am n off0) n FUser.

Section Take.
Variables (L : layout) (s : astate) (g : sptr) (am : ameta) (n off0 : Z).

Local Notation k := (mf_idx am).
Local Notation off := (ef_offm am n off0).
Local Notation am2 := (mf_am2 am n off0).
Local Notation hdr := (mf_hdr am n off0).
Local Notation fr := (mf_fr am n off0).

Definition mf_cnew : list mcell :=
  [MCell (LMem (padd g META_avail)) 4 (VZ (am_avail am - mf_first am));
   MCell (LMem (padd (slot_start am k) (-3))) 1 (VZ (fst hdr));
   MCell (LMem (padd (slot_start am k) (-2))) 2 (VZ (snd hdr))]
  ++ (if off =? 0 then []
      else [MCell (LMem (padd (padd (slot_start am k) (UNIT * off)) (-4))) 1 (VZ 0);
            MCell (LMem (padd (padd (slot_start am k) (UNIT * off)) (-3))) 1 (VZ (hdr_byte3 am2 k fr));
            MCell (LMem (padd (padd (slot_start am k) (UNIT * off)) (-2))) 2 (VZ (hdr_off16 am2 k fr))]).

#[using="Type"] Lemma am2_facts : am_mem am2 = am_mem am /\ stride_of am2 = stride_of am /\ am_last am2 = am_last am /\
  (forall j, j <> k -> 0 <= j -> 0 <= k -> nth_slot am2 j = nth_slot am j) /\
  (0 <= k <= am_last am -> length (am_slots am) = Z.to_nat (am_last am + 1) ->
     nth_slot am2 k = mkSlot (Some hdr) (Some fr)) /\
  meta_bits am2 = meta_bits am /\ am_prev am2 = am_prev am /\ am_next am2 = am_next am /\ am_freed am2 = am_freed am /\
  am_avail am2 = am_avail am - mf_first am /\ slot_start am2 k = slot_start am k.
Proof. LiaFast.lf_pins LiaFast.u0.
  unfold mf_am2, mf_hdr, mf_fr, ef_am, mf_am1, upd_slot. destruct am. cbn. repeat split; try reflexivity.
  - intros j Hj Hj0 Hk0. unfold nth_slot. cbn. rewrite nth_lupd_other; [reflexivity|]. lia.
  - intros Hk Hl. unfold nth_slot. cbn. rewrite nth_lupd_same; [reflexivity|]. cbn in Hl. rewrite Hl. lia.
Qed.

#[using="Type"] Lemma mf_free_slot : WF s -> MT s g = Some (MUsed am) -> am_avail am <> 0 ->
  0 <= k <= am_last am /\ ss_fr (nth_slot am k) = None /\ Z.testbit (am_avail am) k = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros HW HMT Hav.
  assert (Hux : usedX [] s g am) by (unfold usedX, MTX; cbn [memb]; exact HMT).
  pose proof (inv_groups HW g am Hux) as (Gm & Gml & Gsl & _).
  destruct Gm as (Mlast & Maidx & Mlen & Mav0 & Mfr0 & Mdisj & Mabove & Mabove2 & _).
  destruct (lowbit_spec (am_avail am) ltac:(lia)) as (k0 & Hk0 & Hlb & Hbit & Hlow).
  assert (Ek : mf_idx am = k0) by (unfold mf_idx, mf_first; rewrite Hlb; apply ctz32_bit; lia). rewrite Ek.
  assert (Hkl : k0 <= am_last am).
  { destruct (Z_le_gt_dec k0 (am_last am)) as [|Hg]; [assumption|]. rewrite (proj1 (Mabove k0 ltac:(lia))) in Hbit. discriminate. }
  split; [lia|]. split; [|exact Hbit].
  pose proof (Gsl k0 ltac:(lia)) as (_ & _ & S3).
  destruct (ss_fr (nth_slot am k0)) as [f|] eqn:E; [|reflexivity].
  destruct S3 as (Hal & _). unfold allocated in Hal. rewrite Z.lor_spec, Hbit in Hal. discriminate.
Qed.

#[using="Type"] Theorem taken_slot_repr : forall (m m' : byteview) (spz : Z),
  WF s -> repr L s m -> MT s g = Some (MUsed am) -> am_avail am <> 0 ->
  WF (s_mf s g am n off) ->
  (forall rg, In rg (footprint s) -> loc_addr L (fst rg) + snd rg <= spz - 1024) ->
  (forall x, ~ (spz - 1024 <= x < spz) -> ~ (loc_addr L (LMem g) + 24 <= x < loc_addr L (LMem g) + 28) ->
     ~ (loc_addr L (LMem (slot_start am k)) - 3 <= x < loc_addr L (LMem (slot_start am k)) + stride_of am - 4) -> m' x = m x) ->
  (forall x, m x <> None -> m' x <> None) ->
  Forall (cell_holds L m') mf_cnew ->
  repr L (s_mf s g am n off) m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m m' spz HW HR HMT Hav HW' HFP BV BM HNew.
  destruct (mf_free_slot HW HMT Hav) as (Hk & Hfree & Hbit).
  pose proof (am2_facts) as (Em & Es & El & Eoth & Ek & Eb & Ep & Enx & Ef & Eav & Est).
  assert (Hux : usedX [] s g am) by (unfold usedX, MTX; cbn [memb]; exact HMT).
  pose proof (inv_groups HW g am Hux) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
  pose proof G as (Gm & _). destruct Gm as (_ & _ & Mlen & _).
  pose proof (KS_of_WF s HW) as KS.
  pose proof HR as (HL & HC & HFM).
  set (s' := s_mf s g am n off) in *.
  assert (MT' : s' = set_meta s g (MUsed am2)) by reflexivity.
  assert (HL' : layout_ok L s') by (rewrite MT'; apply layout_ok_set_meta; exact HL).
  assert (NewIn : forall c, In c mf_cnew -> In c (image s')).
  { intros c Hc. rewrite MT'. apply (In_image_setm_new s g am am2 c KS HMT).
    unfold mf_cnew in Hc. apply in_app_iff in Hc as [Hc|Hc].
    - destruct Hc as [<-|[<-|[<-|[]]]].
      + left. unfold meta_slot_cells. rewrite Eav. right. right. right. left. reflexivity.
      + right. unfold group_cells. apply in_app_iff. right. apply in_flat_map. exists k. split; [apply In_zseq; lia|].
        unfold slot_cells. rewrite (Ek Hk Mlen), Est. cbn [ss_hdr ss_fr]. rewrite (surjective_pairing hdr).
        cbn [fst snd app In]. tauto.
      + right. unfold group_cells. apply in_app_iff. right. apply in_flat_map. exists k. split; [apply In_zseq; lia|].
        unfold slot_cells. rewrite (Ek Hk Mlen), Est. cbn [ss_hdr ss_fr]. rewrite (surjective_pairing hdr).
        cbn [fst snd app In]. tauto.
    - destruct (off =? 0) eqn:E0; [destruct Hc|].
      right. unfold group_cells. apply in_app_iff. right. apply in_flat_map. exists k. split; [apply In_zseq; lia|].
      unfold slot_cells. rewrite (Ek Hk Mlen), Est. cbn [ss_hdr ss_fr fr_off]. unfold mf_fr at 1. cbn [fr_off]. rewrite E0.
      apply in_app_iff. right. apply in_app_iff. right. exact Hc. }
  apply (repr_from_pre L s s' m m' mf_cnew HR HL').
  - rewrite MT', footprint_set_meta. apply Forall_forall. intros rg Hrg x Hx. apply BM. exact (proj1 (Forall_forall _ _) HFM rg Hrg x Hx).
  - (* [comment removed for export] *)
    intros c Hc. rewrite MT' in Hc. destruct (cov_setm s g am am2 c KS HMT Hc) as [H1|[H2|H3]]; [left; exact H1| |].
    + unfold meta_slot_cells in H2. rewrite Ep, Enx, Em, Eav, Ef, Eb in H2.
      destruct H2 as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
        first [ right; unfold mf_cnew; left; reflexivity
              | left; apply (In_image_used s g am _ KS HMT); left; unfold meta_slot_cells; cbn; tauto ].
    + unfold group_cells in H3. rewrite Em in H3. apply in_app_iff in H3 as [H3|H3].
      * left. apply (In_image_used s g am _ KS HMT). right. unfold group_cells. apply in_app_iff. left.
        assert (Eml : am_maplen am2 = am_maplen am) by (unfold mf_am2, ef_am, mf_am1, upd_slot; destruct am; reflexivity).
        assert (Eai : am_aidx am2 = am_aidx am) by (unfold mf_am2, ef_am, mf_am1, upd_slot; destruct am; reflexivity).
        rewrite Eml, Eai in H3. exact H3.
      * apply in_flat_map in H3 as [j [Hj Hcj]]. rewrite El in Hj. apply In_zseq in Hj.
        destruct (Z.eq_dec j k) as [->|Hjk].
        -- unfold slot_cells in Hcj. rewrite (Ek Hk Mlen), Est in Hcj. cbn [ss_hdr ss_fr] in Hcj.
           apply in_app_iff in Hcj as [Hcj|Hcj].
           ++ left. apply (In_image_used s g am _ KS HMT). right. unfold group_cells. apply in_app_iff. right. apply in_flat_map.
              exists k. split; [apply In_zseq; lia|]. unfold slot_cells. apply in_app_iff. left. exact Hcj.
           ++ right. apply in_app_iff in Hcj as [Hcj|Hcj].
              ** unfold mf_cnew. rewrite (surjective_pairing hdr) in Hcj. cbn [fst snd] in Hcj.
                 destruct Hcj as [<-|[<-|[]]]; [right; left; reflexivity | right; right; left; reflexivity].
              ** unfold mf_fr at 1 in Hcj. cbn [fr_off] in Hcj. unfold mf_cnew. apply in_app_iff. right. exact Hcj.
        -- left. apply (In_image_used s g am _ KS HMT). right. unfold group_cells. apply in_app_iff. right. apply in_flat_map.
           exists j. split; [apply In_zseq; lia|].
           unfold slot_cells in Hcj |- *. rewrite (Eoth j Hjk ltac:(lia) ltac:(lia)) in Hcj.
           assert (Estj : slot_start am2 j = slot_start am j) by (unfold slot_start; rewrite Em, Es; reflexivity).
           rewrite Estj in Hcj. exact Hcj.
  - exact HNew.
  - (* [comment removed for export] *)
    intros c a Hc' Hc Hn Ha. apply BV.
    + destruct (image_in_footprint s L c HW HL Hc) as (rg & Hrg & Hincl). pose proof (HFP rg Hrg) as B.
      unfold range_incl, crange, cell_range, in_rng in *. cbn [fst snd] in *. lia.
    + intros Hav'.
      assert (Ca : In (MCell (LMem (padd g META_avail)) 4 (VZ (am_avail am - mf_first am))) (image s')) by (apply NewIn; unfold mf_cnew; left; reflexivity).
      assert (Hne : c <> MCell (LMem (padd g META_avail)) 4 (VZ (am_avail am - mf_first am))) by (intros ->; apply Hn; unfold mf_cnew; left; reflexivity).
      pose proof (image_pair_disjoint s' L _ _ HW' HL' Hc' Ca Hne) as D.
      unfold ranges_disjoint, cell_range, in_rng in *. cbn [mc_loc mc_w fst snd] in *. rewrite loc_padd in D. unfold META_avail in D. lia.
    + intros Hsl.
      destruct (Z_lt_le_dec a (loc_addr L (LMem (slot_start am (mf_idx am))))) as [Lt|Ge].
      * assert (C3 : In (MCell (LMem (padd (slot_start am (mf_idx am)) (-3))) 1 (VZ (fst (mf_hdr am n off0)))) mf_cnew) by (unfold mf_cnew; right; left; reflexivity).
        assert (C16 : In (MCell (LMem (padd (slot_start am (mf_idx am)) (-2))) 2 (VZ (snd (mf_hdr am n off0)))) mf_cnew) by (unfold mf_cnew; right; right; left; reflexivity).
        destruct (Z_lt_le_dec a (loc_addr L (LMem (slot_start am (mf_idx am))) - 2)) as [A3|A16].
        -- assert (Hne : c <> MCell (LMem (padd (slot_start am (mf_idx am)) (-3))) 1 (VZ (fst (mf_hdr am n off0)))) by (intros ->; exact (Hn C3)).
           pose proof (image_pair_disjoint s' L _ _ HW' HL' Hc' (NewIn _ C3) Hne) as D.
           unfold ranges_disjoint, cell_range, in_rng in *. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat] in *. rewrite loc_padd in D. lia.
        -- assert (Hne : c <> MCell (LMem (padd (slot_start am (mf_idx am)) (-2))) 2 (VZ (snd (mf_hdr am n off0)))) by (intros ->; exact (Hn C16)).
           pose proof (image_pair_disjoint s' L _ _ HW' HL' Hc' (NewIn _ C16) Hne) as D.
           unfold ranges_disjoint, cell_range, in_rng in *. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat] in *. rewrite loc_padd in D. lia.
      * destruct (In_dec mcell_eq_dec c (slot_cells am (mf_idx am))) as [Hk'|Hk'].
        -- unfold slot_cells in Hk'. rewrite Hfree in Hk'. rewrite app_nil_r in Hk'.
           unfold cell_range, in_rng in Ha. cbn [fst snd] in Ha.
           apply in_app_iff in Hk' as [Hk'|Hk'].
           ++ destruct Hk' as [<-|[]]. cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat] in Ha. rewrite loc_padd in Ha. lia.
           ++ destruct (ss_hdr (nth_slot am (mf_idx am))) as [[h3 h16]|]; [|destruct Hk'].
              destruct Hk' as [<-|[<-|[]]]; cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat] in Ha; rewrite loc_padd in Ha; lia.
        -- pose proof (image_outside_free_slot s L c g am (mf_idx am) HW HL Hux Hk Hfree Hc Hk') as D.
           unfold ranges_disjoint, cell_range, free_slot_range, in_rng in D, Ha. cbn [fst snd] in D, Ha.
           lia.
  - intros c Hc. apply image_cell_width with (s := s'). exact Hc.
Qed.

(* [comment removed for export] *)
Definition mf_mnew : list mcell :=
  let e := slot_end am2 k in
  let r := frame_rsv am2 fr in
  (if 0 <? r then [MCell (LMem (padd e (- r))) 1 (VZ 0)] else [])
  ++ (if 5 <=? r then [MCell (LMem (padd e (-4))) 4 (VZ r); MCell (LMem (padd e (-5))) 1 (VZ 0)] else []).

(* [comment removed for export] *)
#[using="Type"] Lemma marker_in_region : forall c, WF s -> In c (markers s) ->
  exists r rg o, region_of s r = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\ mc_loc c = LMem (SP r o) /\
    0 <= o /\ o + Z.of_nat (mc_w c) <= rg_len rg.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros c HW Hc. unfold markers in Hc. apply in_flat_map in Hc as [[g2 a2] [Hu2 Hc]]. cbn [snd] in Hc.
  apply (used_metas_usedX s g2 a2 HW) in Hu2.
  destruct (markers_span s g2 a2 c HW Hu2 Hc) as (q & Eq & Pq & Lo & Hi & _).
  destruct (used_group_region [] None U0 s g2 a2 HW Hu2) as (rg & Hr & Hkd & Hl & Ho & Hext & _).
  destruct q as [r o]. cbn [prid poff] in *. exists r, rg, o. subst r. split; [exact Hr|]. split; [exact Hkd|]. split; [exact Hl|].
  split; [exact Eq|]. unfold group_extent, UNIT, IB in *. split; lia.
Qed.

#[using="Type"] Theorem taken_slot_markers : forall (m m' : byteview) (spz : Z),
  WF s -> repr L s m -> markers_hold L s m -> MT s g = Some (MUsed am) -> am_avail am <> 0 ->
  (forall rg, In rg (footprint s) -> loc_addr L (fst rg) + snd rg <= spz - 1024) ->
  (forall x, ~ (spz - 1024 <= x < spz) -> (forall a, In a (st_areas s) -> ~ (loc_addr L (LMem a) <= x < loc_addr L (LMem a) + 4096)) ->
     ~ (loc_addr L (LMem (slot_start am k)) - 3 <= x < loc_addr L (LMem (slot_start am k)) + stride_of am - 4) -> m' x = m x) ->
  Forall (cell_holds L m') mf_mnew ->
  markers_hold L (s_mf s g am n off) m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m m' spz HW HR HM HMT Hav HFP BV HNew.
  destruct (mf_free_slot HW HMT Hav) as (Hk & Hfree & Hbit).
  pose proof (am2_facts) as (Em & Es & El & Eoth & Ek & Eb & Ep & Enx & Ef & Eav & Est).
  assert (Hux : usedX [] s g am) by (unfold usedX, MTX; cbn [memb]; exact HMT).
  pose proof (inv_groups HW g am Hux) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
  pose proof G as (Gm & _ & Gsl & _). destruct Gm as (Mlast & _ & Mlen & _).
  pose proof HR as (HL & HC & HFM). pose proof HL as (_ & _ & Ldisj & Lrng).
  set (s' := s_mf s g am n off) in *.
  assert (Eloc : forall r, loc_addr L (LMem r) = ly_reg L (prid r) + poff r) by (intros [rr oo]; reflexivity).
  (* [comment removed for export] *)
  assert (OLD : forall c, In c (markers s) -> cell_holds L m' c).
  { intros c Hc. pose proof (proj1 (Forall_forall _ _) HM c Hc) as Hh.
    destruct (marker_in_region c HW Hc) as (r & rg & o & Hr & Hkd & Hl & Ec & Ho & Hw).
    pose proof (footprint_region_In s r rg Hr Hkd Hl) as FR.
    assert (W1 : (1 <= mc_w c)%nat).
    { unfold markers in Hc. apply in_flat_map in Hc as [[g2 a2] [_ Hc]]. cbn [snd] in Hc. unfold meta_markers in Hc.
      apply in_app_iff in Hc as [Hc|[<-|[]]]; [|cbn; lia].
      apply in_flat_map in Hc as [i [_ Hc]]. destruct (ss_fr (nth_slot a2 i)) as [f|]; [|destruct Hc].
      destruct (fr_kind f); [|destruct Hc]. unfold marker_cells in Hc. destruct Hc as [<-|Hc]; [cbn; lia|].
      apply in_app_iff in Hc as [Hc|Hc]; [destruct (0 <? _); [destruct Hc as [<-|[]]; cbn; lia | destruct Hc]|].
      destruct (5 <=? _); [destruct Hc as [<-|[<-|[]]]; cbn; lia | destruct Hc]. }
    apply (cell_holds_frame L m m' c W1 Hh). intros x Hx. apply BV.
    - pose proof (HFP _ FR) as B. cbn [fst snd] in B. rewrite Eloc in B. cbn [prid poff] in B.
      unfold in_rng, cell_range in Hx. rewrite Ec, Eloc in Hx. cbn [fst snd prid poff] in Hx. lia.
    - intros a Ha Hxa. pose proof (inv_areas HW) as (_ & AOK & _).
      destruct (AOK a Ha) as (ra & oa & rga & Ea & _ & Opg & _).
      assert (FA : In (LMem a, PGSZ) (footprint s)) by (unfold footprint; right; apply in_app_iff; left; apply (in_map (fun a1 => (LMem a1, PGSZ))); exact Ha).
      assert (Hne : (LMem a, PGSZ) <> (LMem (SP r 0), rg_len rg)) by (rewrite Ea; intro E; injection E as _ E2; unfold PGSZ in *; lia).
      destruct (pairwise_map_In _ (crange L) _ _ _ Ldisj FA FR Hne) as [D|D];
        unfold ranges_disjoint in D; cbn [crange fst snd] in D; rewrite (Eloc (SP r 0)) in D; cbn [prid poff] in D;
        unfold in_rng, cell_range in Hx; rewrite Ec, Eloc in Hx; cbn [fst snd prid poff] in Hx; unfold PGSZ in *; lia.
    - intros Hsl. pose proof (markers_outside_free_slot s L c g am k HW HL Hux Hk Hfree Hc) as D.
      unfold ranges_disjoint, cell_range, free_slot_range, in_rng in *. cbn [fst snd] in *. lia. }
  (* [comment removed for export] *)
  assert (ND : List.NoDup (keys s)) by exact (proj1 (inv_keys HW)).
  assert (ND' : List.NoDup (keys s')).
  { unfold keys, s', s_mf, set_meta. cbn [st_metas set_metas]. rewrite map_fst_mupdate_In; [exact ND|].
    apply (mlookup_In_keys (st_metas s) g (MUsed am)). exact HMT. }
  apply Forall_forall. intros c Hc.
  destruct (In_markers_inv _ c Hc) as [(h & a & j & f & Hfr' & Kf & Hc') | (h & a & Hua & ->)].
  - destruct (in_frames_inv _ _ _ _ _ Hfr') as (Hua & Hj & Hfj).
    apply (used_metas_iff _ h a ND') in Hua. unfold MT, s', s_mf, set_meta in Hua. cbn [st_metas set_metas] in Hua.
    change (ef_am (mf_am1 am) (mf_idx am) n (ef_offm am n off0)) with (mf_am2 am n off0) in Hua.
    destruct (sptr_eq_dec h g) as [->|Hhg].
    + rewrite mlookup_mupdate_same in Hua. injection Hua as <-.
      destruct (Z.eq_dec j k) as [->|Hjk].
      * rewrite (Ek Hk Mlen) in Hfj. cbn [ss_fr] in Hfj. injection Hfj as <-.
        unfold marker_cells in Hc'. destruct Hc' as [<-|Hc'].
        -- (* [comment removed for export] *)
           assert (Ese : slot_end (mf_am2 am n off0) (mf_idx am) = slot_end am (mf_idx am)).
           { unfold slot_end. rewrite Es, Est. reflexivity. }
           rewrite Ese.
           destruct (Z.eq_dec (mf_idx am) (am_last am)) as [Eql|Nql].
           ++ rewrite Eql. apply OLD. change (MCell (LMem (slot_end am (am_last am))) 1 (VZ 0)) with (gend_cell am).
              apply (In_gend s g am). apply (used_metas_iff s g am ND). exact HMT.
           ++ (* [comment removed for export] *)
              set (ck := MCell (LMem (padd (slot_start am (mf_idx am + 1)) (-4))) 1 (VZ 0)).
              assert (Cin : In ck (image s)).
              { apply (In_image_used s g am _ (KS_of_WF s HW) HMT). right. unfold group_cells. apply in_app_iff. right.
                apply in_flat_map. exists (mf_idx am + 1). split; [apply In_zseq; lia|]. unfold slot_cells. left. reflexivity. }
              assert (Eck : padd (slot_start am (mf_idx am + 1)) (-4) = slot_end am (mf_idx am)).
              { apply sptr_eq_parts; [rewrite prid_padd, prid_slot_start; unfold slot_end; rewrite prid_padd, prid_slot_start; reflexivity|].
                unfold slot_end. rewrite !poff_padd, !poff_slot_start. unfold IB. ring. }
              assert (Hck : cell_holds L m ck) by exact (proj1 (Forall_forall _ _) HC ck Cin).
              unfold ck in Hck. rewrite Eck in Hck.
              apply (cell_holds_frame L m m' (MCell (LMem (slot_end am (mf_idx am))) 1 (VZ 0)) ltac:(cbn; lia) Hck).
              intros x Hx. unfold in_rng, cell_range in Hx. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat] in Hx.
              assert (Ex : x = loc_addr L (LMem (slot_end am (mf_idx am)))) by lia. subst x.
              destruct (used_group_region [] None U0 s g am HW Hux) as (rg & Hr & Hkd & Hl & Ho & Hext & _).
              pose proof (footprint_region_In s _ rg Hr Hkd Hl) as FR.
              pose proof (slot_in_span [] None U0 s HW g am (mf_idx am + 1) Hux ltac:(lia)) as [S1 S1'].
              assert (Epos : loc_addr L (LMem (slot_end am (mf_idx am))) = ly_reg L (prid (am_mem am)) + poff (slot_start am (mf_idx am + 1)) - 4).
              { rewrite <- Eck, Eloc, prid_padd, prid_slot_start, poff_padd. ring. }
              apply BV.
              ** pose proof (HFP _ FR) as B. cbn [fst snd] in B. rewrite Eloc in B. cbn [prid poff] in B.
                 rewrite Epos. rewrite poff_slot_start in *. unfold group_extent, UNIT, IB in *. lia.
              ** intros a Ha Hxa. pose proof (inv_areas HW) as (_ & AOK & _).
                 destruct (AOK a Ha) as (ra & oa & rga & Ea & _ & Opg & _).
                 assert (FA : In (LMem a, PGSZ) (footprint s)) by (unfold footprint; right; apply in_app_iff; left; apply (in_map (fun a1 => (LMem a1, PGSZ))); exact Ha).
                 assert (Hne : (LMem a, PGSZ) <> (LMem (SP (prid (am_mem am)) 0), rg_len rg)) by (rewrite Ea; intro E; injection E as _ E2; unfold PGSZ in *; lia).
                 destruct (pairwise_map_In _ (crange L) _ _ _ Ldisj FA FR Hne) as [D|D];
                   unfold ranges_disjoint in D; cbn [crange fst snd] in D; rewrite (Eloc (SP (prid (am_mem am)) 0)) in D; cbn [prid poff] in D;
                   rewrite Epos in Hxa; rewrite poff_slot_start in *; unfold PGSZ, group_extent, UNIT, IB in *; lia.
              ** rewrite Epos. rewrite Eloc, prid_slot_start. rewrite !poff_slot_start. unfold UNIT, IB. nia.
        -- apply (proj1 (Forall_forall _ _) HNew). exact Hc'.
      * apply OLD. rewrite El in Hj. apply (In_markers s g am j f c).
        -- unfold frames. apply in_flat_map. exists (g, am). split; [apply (used_metas_iff s g am ND); exact HMT|].
           apply in_flat_map. exists j. split; [apply In_zseq; lia|]. rewrite <- (Eoth j Hjk ltac:(lia) ltac:(lia)), Hfj. left. reflexivity.
        -- exact Kf.
        -- unfold marker_cells, slot_end, frame_rsv in *. rewrite Es in Hc'.
           assert (Estj : slot_start (mf_am2 am n off0) j = slot_start am j) by (unfold slot_start; rewrite Em, Es; reflexivity).
           rewrite Estj in Hc'. exact Hc'.
    + rewrite mlookup_mupdate_other in Hua by exact Hhg. apply OLD. apply (In_markers s h a j f c); [|exact Kf | exact Hc'].
      unfold frames. apply in_flat_map. exists (h, a). split; [apply (used_metas_iff s h a ND); exact Hua|].
      apply in_flat_map. exists j. split; [apply In_zseq; lia|]. rewrite Hfj. left. reflexivity.
  - apply (used_metas_iff _ h a ND') in Hua. unfold MT, s', s_mf, set_meta in Hua. cbn [st_metas set_metas] in Hua.
    change (ef_am (mf_am1 am) (mf_idx am) n (ef_offm am n off0)) with (mf_am2 am n off0) in Hua.
    apply OLD. destruct (sptr_eq_dec h g) as [->|Hhg].
    + rewrite mlookup_mupdate_same in Hua. injection Hua as <-.
      replace (gend_cell (mf_am2 am n off0)) with (gend_cell am).
      * apply (In_gend s g am). apply (used_metas_iff s g am ND). exact HMT.
      * unfold gend_cell, slot_end. rewrite El, Es. unfold slot_start. rewrite Em, Es. reflexivity.
    + rewrite mlookup_mupdate_other in Hua by exact Hhg. apply (In_gend s h a). apply (used_metas_iff s h a ND). exact Hua.
Qed.

End Take.
