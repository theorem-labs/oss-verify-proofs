(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk SeqExec AxSymExec3 AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfArith MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfArith OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng MngRepr MngHeap MngWb MngWk MngGeoX MngLt MngSurgery MngExc MngNtfM MngNtfS MngGM.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngHeap.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngMW0 MngMW1 MngMW2 MngMW3 MngNtfPre MngNtfC MngCtx MngCtx2 MngShape MngTake MngTakeX MngOwn MngTakeR MngTakeRX AXG_as1 AXG_amr0 AXG_ag0 AXG_ag1 AXG_ag3p AXG_ag5 AXG_ag6 AXG_ag10 AXG_ag11 AXG_ag12 AXG_ag13.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRepr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWk OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGeoX OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngLt OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngSurgery OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngExc OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfS OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap.MngMWP OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW3 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfPre OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfC OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngCtx OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngCtx2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngShape OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngTake OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngTakeX OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngOwn OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngTakeR OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngTakeRX OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_as1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_amr0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag3p OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag5 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag6 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag10 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag11 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag12 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag13.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Section MN.
Variables (HTOP : Z) (X : list sptr) (U : Z -> Z) (L : layout) (s4 : astate) (m4 : word -> option byte) (sp0 K : Z).
Variables (mt g : sptr) (amg : ameta) (sc cnt0 idx j hb : Z).
Hypothesis C4 : CUT HTOP (mt :: X) (Some (g, idx)) U L s4 m4 sp0 K.
Hypothesis MK4 : markers_hold L s4 (bview SEGS m4).
Hypothesis Ug : usedX (mt :: X) s4 g amg.
Hypothesis Hstr : stride_of amg = class_size j.
Hypothesis Hsc : 0 <= sc <= 47.
Hypothesis Hj : 0 <= j <= 47.
Hypothesis Hcnt : 1 <= cnt0 <= 32.
Hypothesis Hfit : 16 + class_size sc * cnt0 <= class_size j.
Hypothesis Hsz : class_size sc <= 2032.
Hypothesis Hhb : 0 <= hb <= 255.

Local Notation n := (class_size j - IB).
Local Notation p := (padd (slot_start amg idx) 0).
Local Notation am_n := (am_set_links (Some mt) (Some mt) (new_am p sc cnt0 (cnt0 - 1) 0 slot_junk)).
Local Notation s6n := (ag_nest_st mt sc cnt0 g amg idx j s4).
Local Notation st := (loc_addr L (LMem (slot_start amg idx))).
Local Notation memv := (loc_addr L (LMem (am_mem amg))).
Local Notation mta := (loc_addr L (LMem mt)).
Local Notation m6 := (nn_mem m4 idx memv st mta sc cnt0 (usage_of s4 sc) hb).

#[using="HTOP X U sp0 K C4 MK4 Ug Hstr Hsc Hcnt Hfit Hsz"] Theorem markers_nest : markers_hold L s6n (bview SEGS m6).
Proof. LiaFast.lf_pins (fun (HTOP X U sp0 K C4 MK4 Ug Hstr Hsc Hcnt Hfit Hsz : LiaFast.U) => LiaFast.u0).
  pose proof C4 as [HI HX N HG HD HT HTB].
  pose proof (nc_ctx _ _ _ _ _ _ _ N) as Hctx. pose proof (nc_sp1 _ _ _ _ _ _ _ N) as Hsp1. pose proof (nc_sp2 _ _ _ _ _ _ _ N) as Hsp2.
  pose proof (nc_K _ _ _ _ _ _ _ N) as HK1.
  pose proof (layout_of_geo HTOP HTB (mt :: X) (Some (g, idx)) U s4 L HI Hctx HG HD) as HL.
  pose proof (XNU_of_XNM (mt :: X) s4 HX) as XU.
  (* [comment removed for export] *)
  destruct (inv_reserved HI g idx eq_refl) as (am0 & Ug0 & Hidx & Hfr & _).
  pose proof (usedX_fun _ _ _ _ _ Ug0 Ug) as E0. subst am0.
  pose proof (inv_groups HI g amg Ug) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp. pose proof G as ((Mlast & _ & Hlen_sl & _) & _).
  assert (Hlsl : (Z.to_nat idx < length (am_slots amg))%nat) by (rewrite Hlen_sl; lia).
  assert (Mg : mlookup (st_metas s4) g = Some (MUsed amg)) by (destruct (usedX_MT _ _ _ _ Ug) as (E & _); exact E).
  assert (Hgmt : g <> mt).
  { intros E. subst g. destruct (usedX_MT _ _ _ _ Ug) as (_ & Em). unfold memb in Em. cbn [existsb] in Em. rewrite sptr_eqb_refl in Em. discriminate Em. }
  assert (Hmt0 : MT s4 mt = Some MRaw \/ MT s4 mt = Some (MFree None None)) by exact (HX mt (or_introl eq_refl)).
  assert (Hraw : forall am', mlookup (st_metas s4) mt <> Some (MUsed am')).
  { intros am' E. change (mlookup (st_metas s4) mt) with (MT s4 mt) in E. destruct Hmt0 as [E'|E']; rewrite E' in E; discriminate E. }
  (* [comment removed for export] *)
  destruct (used_group_region (mt :: X) (Some (g, idx)) U s4 g amg HI Ug) as (rg & Hr & Hkd & Hl & Ho & Hext & _).
  destruct (HG _ rg Hr Hl) as (G1 & _ & G3 & G4). unfold ranges_disjoint in G4. cbn [fst snd] in G4.
  pose proof (size_classes_range sc ltac:(clear - Hsc; lia)) as Hun. pose proof (class_units sc) as Ecs.
  assert (Hsize : 16 <= class_size sc <= 2032) by (rewrite Ecs in *; clear - Hun Hsz; lia).
  assert (Est : st = ly_reg L (prid (am_mem amg)) + poff (am_mem amg) + 16 + stride_of amg * idx).
  { unfold slot_start. rewrite loc_padd. destruct (am_mem amg) as [rr oo]. cbn [loc_addr prid poff]. unfold UNIT. ring. }
  assert (Hspan : stride_of amg * idx + stride_of amg <= stride_of amg * (am_last amg + 1)) by nia.
  assert (Hgx : poff (am_mem amg) + 16 + stride_of amg * (am_last amg + 1) - 4 + 4 <= rg_len rg).
  { unfold group_extent, UNIT, IB in Hext. lia. }
  assert (Hnest : 16 + class_size sc * cnt0 <= stride_of amg) by (rewrite Hstr; exact Hfit).
  assert (Hsc0 : 16 <= class_size sc * cnt0 <= 2032 * 32) by (clear - Hsize Hcnt; nia).
  assert (Hst : 4096 <= st) by (rewrite Est; clear - G1 Ho Sp Hidx; unfold PGSZ in *; nia).
  assert (Hend : st + 16 + class_size sc * cnt0 <= 2^47) by (rewrite Est; clear - G3 HTB Hgx Hnest Hspan Ho; nia).
  assert (Dst : st + 16 + class_size sc * cnt0 <= 0x10000 \/ 0x97000 <= st - 4).
  { rewrite Est. clear - G4 Hgx Hnest Hspan Ho Sp Hidx. nia. }
  assert (Hkey : In mt (keys s4)) by (destruct Hmt0 as [E'|E']; exact (MT_keys s4 mt _ E')).
  pose proof (nc_mplace _ _ _ _ _ _ _ N mt Hkey) as (Pm1 & Pm2 & Pm3 & Pm4).
  assert (Hmta47 : mta + 40 <= 2^47) by (clear - Pm2 Hsp2 HK1; lia).
  destruct (key_slot_range HTOP (mt :: X) (Some (g, idx)) U s4 L mt HI HG Hkey) as (ar & j' & r' & rga & Har & Hj' & Ear & Epr & Hr' & Hl' & Hk' & A1 & A2 & A3 & A4).
  assert (Dms : mta + 40 <= st - 4 \/ st + 16 + class_size sc * cnt0 <= mta).
  { assert (Hne' : r' <> prid (am_mem amg)) by (intros E; rewrite E in Hr'; rewrite Hr in Hr'; injection Hr' as <-; exact (Hk' Hkd)).
    pose proof (HD r' (prid (am_mem amg)) rga rg Hne' Hr' Hr Hl' Hl) as D. unfold ranges_disjoint in D. cbn [fst snd] in D.
    rewrite A4. rewrite Est. unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. clear - D A2 A3 Hj' Hgx Hnest Hspan Ho Sp Hidx. nia. }
  destruct (nn_reads m4 idx memv st mta sc cnt0 (usage_of s4 sc) hb Hsc Hcnt Hsize Hst Hend Pm1 Hmta47 Pm3 Dst Dms)
    as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RZ).
  (* [comment removed for export] *)
  set (xe := st + 12 + class_size sc * cnt0).
  assert (XE0 : xe = st + stride_of amg - 4 -> m4 (wa xe) = Some (Z_to_bv 8 0)).
  { intros Exe.
    assert (Hh : xe < 0x10000 \/ 0x97000 <= xe) by (rewrite Exe, Est; clear - G4 Hgx Hnest Hspan Ho Sp Hidx; nia).
    assert (Hx' : 0 <= xe < 2^64) by (unfold xe; clear - Hst Hend Hsc0; lia).
    destruct (Z_lt_le_dec idx (am_last amg)) as [Li|Li].
    + (* [comment removed for export] *)
      assert (Hc : In (MCell (LMem (padd (slot_start amg (idx + 1)) (-4))) 1 (VZ 0)) (image s4)).
      { unfold image. apply in_app_iff. right. apply in_app_iff. right. apply in_flat_map. exists (g, amg). split; [exact (used_g_s4 g amg s4 Mg)|].
        cbn [fst snd]. unfold group_cells. apply in_app_iff. right. apply in_flat_map. exists (idx + 1). split; [apply In_zseq; lia|].
        unfold slot_cells. left. reflexivity. }
      pose proof (repr_x_holds L s4 (bview SEGS m4) [] _ (nc_repr _ _ _ _ _ _ _ N) Hc (fun H => H)) as HH.
      assert (Ea : loc_addr L (LMem (padd (slot_start amg (idx + 1)) (-4))) = xe).
      { rewrite Exe, Est, loc_padd. unfold slot_start. rewrite !loc_padd. destruct (am_mem amg) as [rr oo]. cbn [loc_addr prid poff]. unfold UNIT. ring. }
      rewrite <- Ea. apply holds_zero_byte; [exact HH | rewrite Ea; exact Hx' | rewrite Ea; exact Hh].
    + (* [comment removed for export] *)
      assert (Eli : idx = am_last amg) by lia.
      assert (Hc : In (gend_cell amg) (markers s4)).
      { unfold markers. apply in_flat_map. exists (g, amg). split; [exact (used_g_s4 g amg s4 Mg)|]. cbn [snd]. unfold meta_markers. apply in_app_iff. right. left. reflexivity. }
      pose proof (proj1 (Forall_forall _ _) MK4 _ Hc) as HH.
      assert (Ea : loc_addr L (mc_loc (gend_cell amg)) = xe).
      { rewrite Exe. cbn [gend_cell mc_loc]. unfold slot_end. rewrite loc_padd. rewrite <- Eli. unfold IB. ring. }
      unfold gend_cell in HH, Ea. cbn [mc_loc] in Ea. rewrite <- Ea. apply holds_zero_byte; [exact HH | rewrite Ea; exact Hx' | rewrite Ea; exact Hh]. }
  (* [comment removed for export] *)
  assert (OLDB : forall c, In c (markers s4) -> forall x, in_rng (cell_range L c) x -> m6 (wa x) = m4 (wa x)).
  { intros c Hc x Hx.
    destruct (marker_in_region_X (mt :: X) (Some (g, idx)) U s4 L c HI XU Hc) as (r & rgc & o & Hrc & Kc & Lc' & Ec & Oc & Wc).
    pose proof (markers_outside_free_slot_X (mt :: X) (Some (g, idx)) U s4 L c g amg idx HI XU HL Ug Hidx Hfr Hc) as FS.
    destruct (HG r rgc Hrc Lc') as (B1 & _ & B3 & B4). unfold ranges_disjoint in B4. cbn [fst snd] in B4.
    assert (Ex : ly_reg L r + o <= x < ly_reg L r + o + Z.of_nat (mc_w c)).
    { unfold in_rng, cell_range in Hx. rewrite Ec in Hx. change (loc_addr L (LMem (SP r o))) with (ly_reg L r + o) in Hx. cbn [fst snd] in Hx. exact Hx. }
    assert (Hx64 : 0 <= x < 2^64) by (clear - Ex B1 B3 HTB Oc Wc; unfold PGSZ in *; lia).
    unfold ranges_disjoint, free_slot_range, cell_range in FS. rewrite Ec in FS. change (loc_addr L (LMem (SP r o))) with (ly_reg L r + o) in FS. cbn [fst snd] in FS.
    destruct (Z.eq_dec x xe) as [Exe|Nxe].
    { destruct (Z_lt_le_dec xe (st + stride_of amg - 4)) as [Lt|Ge].
      - exfalso. unfold xe in Exe, Lt. clear - FS Ex Exe Lt Hsc0. lia.
      - assert (Ee : xe = st + stride_of amg - 4) by (unfold xe in *; clear - Ge Hnest; lia).
        rewrite Exe. rewrite (XE0 Ee). unfold xe. rewrite (RZ cnt0 ltac:(lia)). reflexivity. }
    apply (nn_out m4 idx memv st mta sc cnt0 (usage_of s4 sc) hb Hsc Hcnt Hsize Hst Hend Pm1 Hmta47 Pm3 Dst Dms x Hx64).
    intros [A|[A|[A|[A|[A|(k & Hk & A)]]]]].
    - (* [comment removed for export] *)
      assert (Hne : r' <> r) by (intros E; rewrite E in Hr'; rewrite Hrc in Hr'; injection Hr' as <-; exact (Hk' Kc)).
      pose proof (HD r' r rga rgc Hne Hr' Hrc Hl' Lc') as D. unfold ranges_disjoint in D. cbn [fst snd] in D.
      rewrite A4 in A. unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. clear - D A A2 A3 Hj' Ex Oc Wc. lia.
    - clear - A B4 Ex Hsc Oc Wc. lia.
    - clear - A B4 Ex Hsc Oc Wc. lia.
    - clear - A FS Ex Sp. lia.
    - clear - A FS Ex Sp. lia.
    - destruct (Z_lt_le_dec k cnt0) as [Lk|Gk].
      + assert (class_size sc * k + class_size sc <= class_size sc * cnt0) by (clear - Lk Hk Hsize; nia). clear - A FS Ex Lk Hk Hnest Hsize H. lia.
      + apply Nxe. unfold xe. rewrite A. replace k with cnt0 by lia. reflexivity. }
  (* [comment removed for export] *)
  assert (ND4 : List.NoDup (keys s4)) by exact (proj1 (inv_keys HI)).
  assert (Kg : In g (keys s4)) by exact (mlookup_In_keys _ _ _ Mg).
  assert (Ekeys : keys s6n = keys s4).
  { unfold keys, ag_nest_st. rewrite (sn_metas mt g amg sc cnt0 idx n s4).
    rewrite map_fst_mupdate_In; [apply map_fst_mupdate_In; exact Kg|]. rewrite map_fst_mupdate_In by exact Kg. exact Hkey. }
  assert (ND6 : List.NoDup (keys s6n)) by (rewrite Ekeys; exact ND4).
  pose proof (upd_slot_fields amg idx (nest_slot amg idx n)) as (Fm & Fl & Fsc & Fml & Fst & Fex & Fss).
  assert (EMC : forall i fr, marker_cells (amg' amg idx n) i fr = marker_cells amg i fr).
  { intros i fr. unfold marker_cells, slot_end, frame_rsv, amg'. rewrite Fst, Fss. reflexivity. }
  assert (EGC : gend_cell (amg' amg idx n) = gend_cell amg) by (unfold gend_cell, slot_end, amg'; rewrite Fl, Fst, Fss; reflexivity).
  assert (INCL : forall c, In c (markers s6n) -> In c (markers s4) \/ c = gend_cell am_n).
  { intros c Hc. destruct (In_markers_inv s6n c Hc) as [(h & ah & i & fr & HF & Kf & Hc') | (h & ah & Hu & ->)].
    - left. destruct (in_frames_inv s6n h ah i fr HF) as (Hu & Hi & Hfi).
      apply (used_metas_iff s6n h ah ND6) in Hu. unfold MT, ag_nest_st in Hu.
      destruct (sptr_eq_dec h mt) as [->|Hhm].
      + rewrite (sn_lookup_mt mt g amg sc cnt0 idx n s4) in Hu. injection Hu as <-.
        exfalso. unfold nth_slot in Hfi. cbn [am_slots am_set_links new_am] in Hfi. rewrite nth_repeat' in Hfi. destruct (Nat.ltb _ _); discriminate Hfi.
      + destruct (sptr_eq_dec h g) as [->|Hhg].
        * rewrite (sn_lookup_g mt g amg sc cnt0 idx n s4 Hgmt) in Hu. injection Hu as <-.
          unfold amg' in Hi, Hfi. rewrite Fl in Hi. rewrite nth_slot_upd_slot in Hfi by lia.
          destruct (i =? idx) eqn:Ei; [injection Hfi as <-; cbn [fr_kind] in Kf; discriminate Kf|].
          rewrite EMC in Hc'. apply (In_markers s4 g amg i fr c); [|exact Kf | exact Hc'].
          unfold frames. apply in_flat_map. exists (g, amg). split; [exact (used_g_s4 g amg s4 Mg)|]. apply in_flat_map. exists i.
          split; [apply In_zseq; lia|]. cbn [fst snd]. rewrite Hfi. left. reflexivity.
        * rewrite (sn_lookup mt g amg sc cnt0 idx n s4 h Hhm Hhg) in Hu.
          apply (In_markers s4 h ah i fr c); [|exact Kf | exact Hc'].
          unfold frames. apply in_flat_map. exists (h, ah). split; [apply (used_metas_iff s4 h ah ND4); exact Hu|]. apply in_flat_map. exists i.
          split; [apply In_zseq; lia|]. cbn [fst snd]. rewrite Hfi. left. reflexivity.
    - apply (used_metas_iff s6n h ah ND6) in Hu. unfold MT, ag_nest_st in Hu.
      destruct (sptr_eq_dec h mt) as [->|Hhm].
      + right. rewrite (sn_lookup_mt mt g amg sc cnt0 idx n s4) in Hu. injection Hu as <-. reflexivity.
      + left. destruct (sptr_eq_dec h g) as [->|Hhg].
        * rewrite (sn_lookup_g mt g amg sc cnt0 idx n s4 Hgmt) in Hu. injection Hu as <-. rewrite EGC. exact (In_gend s4 g amg (used_g_s4 g amg s4 Mg)).
        * rewrite (sn_lookup mt g amg sc cnt0 idx n s4 h Hhm Hhg) in Hu. exact (In_gend s4 h ah (proj2 (used_metas_iff s4 h ah ND4) Hu)). }
  (* [comment removed for export] *)
  assert (NEW : cell_holds L (bview SEGS m6) (gend_cell am_n)).
  { assert (Hsize_st : stride_of am_n = class_size sc).
    { unfold stride_of. cbn [am_last am_sc am_maplen am_set_links new_am]. replace (0 =? 0) with true by reflexivity. cbn [negb andb].
      destruct (cnt0 - 1 =? 0); reflexivity. }
    assert (LK : loc_addr L (mc_loc (gend_cell am_n)) = xe).
    { cbn [gend_cell mc_loc]. unfold slot_end. rewrite loc_padd, Hsize_st.
      assert (E1 : slot_start am_n (am_last am_n) = padd p (UNIT + class_size sc * (cnt0 - 1))).
      { unfold slot_start at 1. rewrite Hsize_st. reflexivity. }
      rewrite E1, !loc_padd. unfold xe, UNIT, IB. ring. }
    unfold gend_cell in LK |- *. cbn [mc_loc] in LK.
    apply (holds_read L m6 _ 1 _ 0); [intros z E; discriminate E | lia | rewrite LK; unfold xe; clear - Hst Hsc0; lia
                                     | rewrite LK; unfold xe; clear - Hend Hsc0; cbn [Z.of_nat Pos.of_succ_nat]; lia | reflexivity |].
    intros k' Hkk. assert (k' = 0%nat) as -> by lia. rewrite LK, Z.add_0_r. unfold xe. rewrite (RZ cnt0 ltac:(lia)). reflexivity. }
  unfold markers_hold. apply Forall_forall. intros c Hc. destruct (INCL c Hc) as [H | ->]; [|exact NEW].
  pose proof (proj1 (Forall_forall _ _) MK4 c H) as HH.
  assert (W1 : (1 <= mc_w c)%nat).
  { unfold markers in H. apply in_flat_map in H as [[g2 a2] [_ H]]. cbn [snd] in H. unfold meta_markers in H.
    apply in_app_iff in H as [H|[<-|[]]]; [|cbn; lia].
    apply in_flat_map in H as [i [_ H]]. destruct (ss_fr (nth_slot a2 i)) as [f|]; [|destruct H].
    destruct (fr_kind f); [|destruct H]. unfold marker_cells in H. destruct H as [<-|H]; [cbn; lia|].
    apply in_app_iff in H as [H|H]; [destruct (0 <? _); [destruct H as [<-|[]]; cbn; lia | destruct H]|].
    destruct (5 <=? _); [destruct H as [<-|[<-|[]]]; cbn; lia | destruct H]. }
  apply (cell_holds_frame L (bview SEGS m4) (bview SEGS m6) c W1 HH). intros a Ha. apply MngWb.bview_ext. exact (OLDB c H a Ha).
Qed.
End MN.
