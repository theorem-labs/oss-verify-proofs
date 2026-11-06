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
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngMW0 MngMW1 MngMW2 MngMW3 MngNtfPre MngNtfC MngCtx MngCtx2 MngShape MngTake MngTakeX MngOwn AXG_as1 AXG_amr0 AXG_ag0 AXG_ag1 AXG_ag3p AXG_ag5 AXG_ag6 AXG_ag10 AXG_ag11 AXG_ag12.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRepr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWk OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGeoX OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngLt OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngSurgery OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngExc OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfS OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap.MngMWP OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW3 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfPre OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfC OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngCtx OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngCtx2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngShape OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngTake OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngTakeX OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngOwn OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_as1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_amr0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag3p OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag5 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag6 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag10 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag11 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag12.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Lemma segs_none_heap : forall a, (a < 0x10000 \/ 0x97000 <= a) -> find_segment SEGS a 1 = None.
Proof.
  intros a Ha.
  assert (H : forallb (fun sg => (0x10000 <=? Z.of_N (seg_base sg)) && (Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? 0x97000)) SEGS = true)
    by (vm_compute; reflexivity).
  revert H. generalize SEGS as l. induction l as [|sg t IH]; intros H; [reflexivity|]. cbn [forallb] in H. apply andb_true_iff in H as [H1 H2].
  apply andb_true_iff in H1 as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2. cbn [find_segment].
  replace ((Z.of_N (seg_base sg) <=? a) && (a + 1 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) with false
    by (symmetry; apply andb_false_iff; destruct Ha; [left; apply Z.leb_gt; lia | right; apply Z.leb_gt; lia]).
  exact (IH H2).
Qed.

(* [comment removed for export] *)
Lemma heap_byte : forall (m : word -> option byte) a z, 0 <= a < 2^64 -> (a < 0x10000 \/ 0x97000 <= a) ->
  bview SEGS m a = Some z -> m (wa a) = Some (Z_to_bv 8 z).
Proof.
  intros m a z Ha Hh H. destruct (bview_some SEGS m a z H) as (_ & Hw & Hr).
  unfold wview in Hw. destruct (m (wa a)) as [b|] eqn:E.
  - cbn [ov_read_bytes] in Hr. rewrite E in Hr. injection Hr as <-. reflexivity.
  - exfalso. apply Hw. rewrite (u_wa_small a) by lia. rewrite segs_none_heap by exact Hh. reflexivity.
Qed.

Lemma holds_zero_byte : forall L (m : word -> option byte) l, cell_holds L (bview SEGS m) (MCell l 1 (VZ 0)) ->
  0 <= loc_addr L l < 2^64 -> (loc_addr L l < 0x10000 \/ 0x97000 <= loc_addr L l) -> m (wa (loc_addr L l)) = Some (Z_to_bv 8 0).
Proof.
  intros L m l H Hr Hh. unfold cell_holds in H. cbn [mc_loc mc_w mc_val] in H.
  specialize (H 0%nat ltac:(lia)). rewrite Z.add_0_r in H. exact (heap_byte m _ _ Hr Hh H).
Qed.

Section CUTN.
Variables (UB0 : Z -> Prop) (HTOP : Z) (X : list sptr) (U : Z -> Z) (L : layout) (s4 : astate) (m4 : word -> option byte) (sp0 K : Z).
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
Hypothesis NX : ~ In mt X.
Hypothesis Hhb : 0 <= hb <= 255.
Hypothesis UBI : forall x, UB0 x -> in_user_block L s4 x.

Local Notation n := (class_size j - IB).
Local Notation p := (padd (slot_start amg idx) 0).
Local Notation s6n := (ag_nest_st mt sc cnt0 g amg idx j s4).
Local Notation st := (loc_addr L (LMem (slot_start amg idx))).
Local Notation memv := (loc_addr L (LMem (am_mem amg))).
Local Notation mta := (loc_addr L (LMem mt)).
Local Notation m6 := (nn_mem m4 idx memv st mta sc cnt0 (usage_of s4 sc) hb).

Hypothesis HI6 : Inv X (Some (mt, 0)) U s6n.

#[using="C4 MK4 Ug Hstr Hsc Hcnt Hfit Hsz NX Hhb UBI HI6"] Theorem cut_nest : CUT HTOP X (Some (mt, 0)) U L s6n m6 sp0 K /\ GROWX UB0 sp0 K L s4 m4 L s6n m6.
Proof. LiaFast.lf_pins (fun (C4 MK4 Ug Hstr Hsc Hcnt Hfit Hsz NX Hhb UBI HI6 : LiaFast.U) => LiaFast.u0).
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
  pose proof (inv_ctx HI) as (LA & LU & _ & _ & C5 & _).
  (* [comment removed for export] *)
  destruct (used_group_region (mt :: X) (Some (g, idx)) U s4 g amg HI Ug) as (rg & Hr & Hkd & Hl & Ho & Hext & _).
  destruct (HG _ rg Hr Hl) as (G1 & _ & G3 & G4). unfold ranges_disjoint in G4. cbn [fst snd] in G4.
  pose proof (size_classes_range sc ltac:(clear - Hsc; lia)) as Hun. pose proof (class_units sc) as Ecs.
  assert (Hsize : 16 <= class_size sc <= 2032) by (rewrite Ecs in *; clear - Hun Hsz; lia).
  assert (Est : st = ly_reg L (prid (am_mem amg)) + poff (am_mem amg) + 16 + stride_of amg * idx).
  { unfold slot_start. rewrite loc_padd. destruct (am_mem amg) as [rr oo]. cbn [loc_addr prid poff]. unfold UNIT. ring. }
  assert (Emem : memv = ly_reg L (prid (am_mem amg)) + poff (am_mem amg)) by (destruct (am_mem amg) as [rr oo]; reflexivity).
  assert (Hspan : stride_of amg * idx + stride_of amg <= stride_of amg * (am_last amg + 1)) by nia.
  assert (Hgx : poff (am_mem amg) + 16 + stride_of amg * (am_last amg + 1) - 4 + 4 <= rg_len rg).
  { unfold group_extent, UNIT, IB in Hext. lia. }
  assert (Hnest : 16 + class_size sc * cnt0 <= stride_of amg) by (rewrite Hstr; exact Hfit).
  assert (Hsc0 : 16 <= class_size sc * cnt0 <= 2032 * 32) by (clear - Hsize Hcnt; nia).
  assert (Hst : 4096 <= st) by (rewrite Est; clear - G1 Ho Sp Hidx; unfold PGSZ in *; nia).
  assert (Hend : st + 16 + class_size sc * cnt0 <= 2^47) by (rewrite Est; clear - G3 HTB Hgx Hnest Hspan Ho; nia).
  assert (Dst : st + 16 + class_size sc * cnt0 <= 0x10000 \/ 0x97000 <= st - 4).
  { rewrite Est. clear - G4 Hgx Hnest Hspan Ho Sp Hidx. nia. }
  (* [comment removed for export] *)
  assert (Hkey : In mt (keys s4)) by (destruct Hmt0 as [E'|E']; exact (MT_keys s4 mt _ E')).
  pose proof (nc_mplace _ _ _ _ _ _ _ N mt Hkey) as (Pm1 & Pm2 & Pm3 & Pm4).
  assert (Hmta47 : mta + 40 <= 2^47) by (clear - Pm2 Hsp2 HK1; lia).
  destruct (key_slot_range HTOP (mt :: X) (Some (g, idx)) U s4 L mt HI HG Hkey) as (ar & j' & r' & rga & Har & Hj' & Ear & Epr & Hr' & Hl' & Hk' & A1 & A2 & A3 & A4).
  assert (Dms : mta + 40 <= st - 4 \/ st + 16 + class_size sc * cnt0 <= mta).
  { assert (Hne' : r' <> prid (am_mem amg)) by (intros E; rewrite E in Hr'; rewrite Hr in Hr'; injection Hr' as <-; exact (Hk' Hkd)).
    pose proof (HD r' (prid (am_mem amg)) rga rg Hne' Hr' Hr Hl' Hl) as D. unfold ranges_disjoint in D. cbn [fst snd] in D.
    rewrite A4. rewrite Est. unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. clear - D A2 A3 Hj' Hgx Hnest Hspan Ho Sp Hidx. nia. }
  assert (HgX : ~ In g X).
  { intros Hin. destruct (usedX_MT _ _ _ _ Ug) as (_ & Em). unfold memb in Em. cbn [existsb] in Em. apply orb_false_iff in Em as [_ Em].
    assert (T : existsb (sptr_eqb g) X = true) by (apply existsb_exists; exists g; split; [exact Hin | apply sptr_eqb_refl]).
    rewrite T in Em. discriminate Em. }
  (* [comment removed for export] *)
  assert (Hhdr : (st - memv - 16) / 16 = (stride_of amg * idx) / UNIT) by (rewrite Est, Emem; unfold UNIT; f_equal; ring).
  destruct (nn_reads m4 idx memv st mta sc cnt0 (usage_of s4 sc) hb Hsc Hcnt Hsize Hst Hend Pm1 Hmta47 Pm3 Dst Dms)
    as (R0 & R8 & R16 & R24 & R28 & R32 & RU & RA & RG0 & RG8 & RH3 & RH16 & RZ).
  assert (KS6 : KS s6n) by exact (KS_of_Inv X (Some (mt, 0)) U s6n HI6).
  assert (Lc : forall o, loc_addr L (LCtx o) = 614104 + o) by (intros o; cbn [loc_addr]; rewrite Hctx; reflexivity).
  assert (LP : forall d, loc_addr L (LMem (padd mt d)) = mta + d) by (intros d; rewrite loc_padd; reflexivity).
  assert (LS : forall d, loc_addr L (LMem (padd (slot_start amg idx) d)) = st + d) by (intros d; rewrite loc_padd; reflexivity).
  (* [comment removed for export] *)
  set (xe := st + 12 + class_size sc * cnt0).
  set (EX := fun x => x = xe /\ x < st + stride_of amg - 4).
  apply (silent_stepX UB0 HTOP (mt :: X) (Some (g, idx)) U X (Some (mt, 0)) U L s4 s6n m4 m6 sp0 K (CnewN mt g amg sc cnt0 idx n s4) EX C4).
  - exact HI6.
  - intros x Hx. unfold MT, ag_nest_st. rewrite (sn_lookup mt g amg sc cnt0 idx n s4 x) by (first [intros E; subst x; exact (NX Hx) | intros E; subst x; exact (HgX Hx)]).
    exact (HX x (or_intror Hx)).
  - reflexivity.
  - intros f Hf. left. exact Hf.
  - exact (covN mt g amg sc cnt0 idx n s4 Hgmt Mg Hidx Hlsl LA LU).
  - exact (inN mt g amg sc cnt0 idx n s4 Hgmt Hraw Hidx Hlsl Hsc LA LU KS6).
  - intros c Hc. exact (revN mt g amg sc cnt0 idx n s4 Hgmt Mg Hraw Hidx Hlsl Hfr L c Hc).
  - (* [comment removed for export] *)
    assert (Hsize_st : stride_of (am_set_links (Some mt) (Some mt) (new_am p sc cnt0 (cnt0 - 1) 0 slot_junk)) = class_size sc).
    { unfold stride_of. cbn [am_last am_sc am_maplen am_set_links new_am]. replace (0 =? 0) with true by reflexivity. cbn [negb andb].
      destruct (cnt0 - 1 =? 0); reflexivity. }
    unfold CnewN. apply Forall_cons; [|apply Forall_cons; [|apply Forall_app; split; [|apply Forall_app; split]]].
    + unfold usg_cell. apply (holds_read L m6 _ 8 _ (cnt0 + usage_of s4 sc)); [intros z E; discriminate E | lia | rewrite Lc; unfold CTX_usage; lia
                                                                           | rewrite Lc; unfold CTX_usage; cbn [Z.of_nat Pos.of_succ_nat]; lia | |].
      * cbn [sval_num]. unfold ag_nest_st, ins_st. cbn [st_usage set_active set_metas set_usage]. unfold zset. rewrite nth_zupd_same by (cbn [st_usage ef_grp_st set_metas]; rewrite LU; lia).
        change (usage_of (ef_grp_st g amg idx n s4) sc) with (usage_of s4 sc). rewrite Z.add_comm. reflexivity.
      * intros k Hk. rewrite Lc. unfold CTX_usage. rewrite Z2Nat.id by lia. replace (614104 + (464 + 8 * sc) + Z.of_nat k) with (8 * sc + 614568 + Z.of_nat k) by ring.
        exact (RU k Hk).
    + unfold act_cell. apply (holds_read L m6 _ 8 _ mta); [intros z E; discriminate E | lia | rewrite Lc; unfold CTX_active; lia
                                                          | rewrite Lc; unfold CTX_active; cbn [Z.of_nat Pos.of_succ_nat]; lia | reflexivity |].
      intros k Hk. rewrite Lc. unfold CTX_active. rewrite Z2Nat.id by lia. replace (614104 + (80 + 8 * sc) + Z.of_nat k) with (8 * sc + 614184 + Z.of_nat k) by ring.
      exact (RA k Hk).
    + cbn [meta_slot_cells am_prev am_next am_mem am_avail am_freed am_last am_sc am_maplen am_aidx am_set_links new_am optr].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]]].
      * apply (holds_read L m6 _ 8 _ mta); [intros z E; discriminate E | lia | rewrite LP; unfold META_prev; lia | rewrite LP; unfold META_prev; cbn [Z.of_nat Pos.of_succ_nat]; lia | reflexivity |].
        intros k Hk. rewrite LP. unfold META_prev. exact (R0 k Hk).
      * apply (holds_read L m6 _ 8 _ mta); [intros z E; discriminate E | lia | rewrite LP; unfold META_next; lia | rewrite LP; unfold META_next; cbn [Z.of_nat Pos.of_succ_nat]; lia | reflexivity |].
        intros k Hk. rewrite LP. unfold META_next. exact (R8 k Hk).
      * apply (holds_read L m6 _ 8 _ st); [intros z E; discriminate E | lia | rewrite LP; unfold META_mem; lia | rewrite LP; unfold META_mem; cbn [Z.of_nat Pos.of_succ_nat]; lia | |].
        { cbn [sval_num]. rewrite LS. rewrite Z.add_0_r. reflexivity. }
        { intros k Hk. rewrite LP. unfold META_mem. exact (R16 k Hk). }
      * apply (holds_read L m6 _ 4 _ (2 ^ (cnt0 - 1 + 1) - 2)); [intros z E; discriminate E | lia | rewrite LP; unfold META_avail; lia | rewrite LP; unfold META_avail; cbn [Z.of_nat Pos.of_succ_nat]; lia | |].
        { cbn [sval_num]. rewrite ones_sub. reflexivity. }
        { intros k Hk. rewrite LP. unfold META_avail. exact (R24 k Hk). }
      * apply (holds_read L m6 _ 4 _ ((2 ^ cnt0 - 1) - (2 ^ (cnt0 - 1 + 1) - 1))); [intros z E; discriminate E | lia | rewrite LP; unfold META_freed; lia
                                                                                  | rewrite LP; unfold META_freed; cbn [Z.of_nat Pos.of_succ_nat]; lia | |].
        { cbn [sval_num]. unfold ones. replace (cnt0 - 1 + 1) with cnt0 by ring. reflexivity. }
        { intros k Hk. rewrite LP. unfold META_freed. exact (R28 k Hk). }
      * apply (holds_read L m6 _ 8 _ (64 * sc + cnt0 + 31)); [intros z E; discriminate E | lia | rewrite LP; unfold META_bits; lia | rewrite LP; unfold META_bits; cbn [Z.of_nat Pos.of_succ_nat]; lia | |].
        { cbn [sval_num]. unfold meta_bits. cbn [am_last am_sc am_maplen am_set_links new_am]. f_equal. ring. }
        { intros k Hk. rewrite LP. unfold META_bits. exact (R32 k Hk). }
    + unfold hdr_cells. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (holds_read L m6 _ 1 _ (idx + 192)); [intros z E; discriminate E | lia | rewrite LS; lia | rewrite LS; cbn [Z.of_nat Pos.of_succ_nat]; lia | reflexivity |].
        intros k Hk. assert (k = 0%nat) as -> by lia. rewrite LS. rewrite Z.add_0_r. exact RH3.
      * apply (holds_read L m6 _ 2 _ ((st - memv - 16) / 16)); [intros z E; discriminate E | lia | rewrite LS; lia | rewrite LS; cbn [Z.of_nat Pos.of_succ_nat]; lia | |].
        { cbn [sval_num nest_hdr snd]. rewrite Hhdr. reflexivity. }
        { intros k Hk. rewrite LS. replace (st + -2 + Z.of_nat k) with (st - 2 + Z.of_nat k) by ring. exact (RH16 k Hk). }
    + unfold group_cells. cbn [am_mem am_maplen am_aidx am_last am_set_links new_am Z.eqb]. apply Forall_cons; [|apply Forall_cons; [|]].
      * apply (holds_read L m6 _ 8 _ mta); [intros z E; discriminate E | lia | rewrite LS; lia | rewrite LS; cbn [Z.of_nat Pos.of_succ_nat]; lia | reflexivity |].
        intros k Hk. rewrite LS. exact (RG0 k Hk).
      * unfold cell_holds. cbn [mc_loc mc_w mc_val]. rewrite loc_padd, LS. rewrite Z.add_0_r.
        exists ((cnt0 - 1 + 32 * Z.shiftr hb 5) mod 256). split.
        { rewrite (MngWb.bview_some_byte SEGS m6 (st + 8) _ ltac:(lia) RG8). f_equal. unfold word_to_le_bytes. rewrite u_wa_small.
          - cbn [Z_to_le_bytes nth]. rewrite Z_to_bv_unsigned. reflexivity.
          - assert (Hsh : 0 <= Z.shiftr hb 5 <= 7) by (rewrite Z.shiftr_div_pow2 by lia; change (2^5) with 32; split; [apply Z.div_pos; lia | assert (hb / 32 < 8) by (apply Z.div_lt_upper_bound; lia); lia]).
            clear - Hsh Hcnt. lia. }
        { assert (Hsh : 0 <= Z.shiftr hb 5 <= 7) by (rewrite Z.shiftr_div_pow2 by lia; change (2^5) with 32; split; [apply Z.div_pos; lia | assert (hb / 32 < 8) by (apply Z.div_lt_upper_bound; lia); lia]).
          rewrite (Z.mod_small (cnt0 - 1 + 32 * Z.shiftr hb 5) 256) by (clear - Hsh Hcnt; lia). replace (cnt0 - 1 + 32 * Z.shiftr hb 5) with ((cnt0 - 1) + Z.shiftr hb 5 * 32) by ring.
          rewrite Z.mod_add by lia. apply Z.mod_small. clear - Hcnt. lia. }
      * apply Forall_forall. intros c Hc. apply in_flat_map in Hc as (k & Hk & Hck). apply In_zseq in Hk.
        assert (Hsl : nth_slot (am_set_links (Some mt) (Some mt) (new_am p sc cnt0 (cnt0 - 1) 0 slot_junk)) k = slot_junk).
        { unfold nth_slot. cbn [am_slots am_set_links new_am]. rewrite nth_repeat'. destruct (Nat.ltb (Z.to_nat k) (Z.to_nat cnt0)); reflexivity. }
        unfold slot_cells in Hck. rewrite Hsl in Hck. cbn [ss_hdr ss_fr slot_junk app In] in Hck. destruct Hck as [<-|[]].
        assert (LK : loc_addr L (LMem (padd (slot_start (am_set_links (Some mt) (Some mt) (new_am p sc cnt0 (cnt0 - 1) 0 slot_junk)) k) (-4))) = st + 12 + class_size sc * k).
        { rewrite loc_padd.
          assert (E1 : slot_start (am_set_links (Some mt) (Some mt) (new_am p sc cnt0 (cnt0 - 1) 0 slot_junk)) k = padd p (UNIT + class_size sc * k)).
          { unfold slot_start at 1. rewrite Hsize_st. reflexivity. }
          rewrite E1, !loc_padd. unfold UNIT. ring. }
        apply (holds_read L m6 _ 1 _ 0); [intros z E; discriminate E | lia | rewrite LK; clear - Hst Hk Hsize; nia | rewrite LK; clear - Hend Hk Hsize Hsc0; cbn [Z.of_nat Pos.of_succ_nat]; nia | reflexivity |].
        intros k' Hkk. assert (k' = 0%nat) as -> by lia. rewrite LK, Z.add_0_r. rewrite (RZ k ltac:(lia)). reflexivity.
  - apply nn_grows.
  - (* [comment removed for export] *)
    intros x (Ex & Hxl). subst x.
    assert (Hxin : st - 3 <= xe < st + stride_of amg - 4) by (split; [unfold xe; clear - Hsc0; lia | exact Hxl]).
    assert (FRx : in_rng (free_slot_range L amg idx) xe) by (unfold in_rng, free_slot_range; cbn [fst snd]; clear - Hxin; lia).
    split; [|split].
    + intros c Hc Hin. destruct (In_dec mcell_eq_dec c (slot_cells amg idx)) as [Hsl|Hnsl].
      * unfold slot_cells in Hsl. rewrite Hfr in Hsl. cbn [app] in Hsl. rewrite app_nil_r in Hsl.
        unfold in_rng, cell_range in Hin. cbn [fst snd] in Hin.
        destruct Hsl as [<-|Hsl]; [cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat] in Hin; rewrite LS in Hin; unfold xe in Hin; clear - Hin Hsc0; lia|].
        destruct (ss_hdr (nth_slot amg idx)) as [[h3 h16]|]; [|destruct Hsl].
        destruct Hsl as [<-|[<-|[]]]; cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat] in Hin; rewrite LS in Hin; unfold xe in Hin; clear - Hin Hsc0; lia.
      * pose proof (image_outside_free_slot_X (mt :: X) (Some (g, idx)) U s4 L HI XU HL c g amg idx Ug Hidx Hfr Hc Hnsl) as D.
        unfold ranges_disjoint, in_rng in *. cbn [fst snd] in *. unfold free_slot_range in *. cbn [fst snd] in *. clear - D Hin FRx. lia.
    + exists (prid (am_mem amg)), rg. split; [exact Hr|]. split; [exact Hl|]. split; [exact Hkd|].
      unfold xe. rewrite Est. clear - Hgx Hnest Hspan Ho Sp Hidx Hsc0. nia.
    + intros HU. destruct (UBI xe HU) as (b & Hb & Hbx).
      pose proof (free_slot_outside_blocks_X (mt :: X) (Some (g, idx)) U s4 L HI XU HL g amg idx b Ug Hidx Hfr Hb) as D.
      unfold ranges_disjoint, block_range, in_rng, free_slot_range in *. cbn [fst snd] in *. clear - D Hbx FRx. lia.
  - (* [comment removed for export] *)
    intros x Hx Hne. right.
    assert (INM : forall c, In c (meta_slot_cells mt (Some (MUsed (am_set_links (Some mt) (Some mt) (new_am p sc cnt0 (cnt0 - 1) 0 slot_junk))))) ->
                    In c (CnewN mt g amg sc cnt0 idx n s4)).
    { intros c Hc. unfold CnewN. apply in_app_iff. right. apply in_app_iff. left. exact Hc. }
    assert (ING : forall c, In c (group_cells mt (am_set_links (Some mt) (Some mt) (new_am p sc cnt0 (cnt0 - 1) 0 slot_junk))) ->
                    In c (CnewN mt g amg sc cnt0 idx n s4)).
    { intros c Hc. unfold CnewN. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. exact Hc. }
    assert (INH : forall c, In c (hdr_cells amg idx) -> In c (CnewN mt g amg sc cnt0 idx n s4)).
    { intros c Hc. unfold CnewN. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. exact Hc. }
    destruct (range_dec x mta 40) as [M|M].
    { left. destruct (range_dec x mta 8) as [M1|M1].
      { exists (MCell (LMem (padd mt META_prev)) 8 (optr (Some mt))). split; [apply INM; cbn [meta_slot_cells am_prev In am_set_links]; left; reflexivity|].
        unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd]. rewrite LP. unfold META_prev. cbn [Z.of_nat Pos.of_succ_nat]. clear - M1; lia. }
      destruct (range_dec x (mta + 8) 8) as [M2|M2].
      { exists (MCell (LMem (padd mt META_next)) 8 (optr (Some mt))). split; [apply INM; cbn [meta_slot_cells am_next In am_set_links]; right; left; reflexivity|].
        unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd]. rewrite LP. unfold META_next. cbn [Z.of_nat Pos.of_succ_nat]. clear - M2; lia. }
      destruct (range_dec x (mta + 16) 8) as [M3|M3].
      { eexists. split; [apply INM; cbn [meta_slot_cells In]; right; right; left; reflexivity|].
        unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd]. rewrite LP. unfold META_mem. cbn [Z.of_nat Pos.of_succ_nat]. clear - M3; lia. }
      destruct (range_dec x (mta + 24) 4) as [M4|M4].
      { eexists. split; [apply INM; cbn [meta_slot_cells In]; right; right; right; left; reflexivity|].
        unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd]. rewrite LP. unfold META_avail. cbn [Z.of_nat Pos.of_succ_nat]. clear - M4; lia. }
      destruct (range_dec x (mta + 28) 4) as [M5|M5].
      { eexists. split; [apply INM; cbn [meta_slot_cells In]; right; right; right; right; left; reflexivity|].
        unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd]. rewrite LP. unfold META_freed. cbn [Z.of_nat Pos.of_succ_nat]. clear - M5; lia. }
      eexists. split; [apply INM; cbn [meta_slot_cells In]; right; right; right; right; right; left; reflexivity|].
      unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd]. rewrite LP. unfold META_bits. cbn [Z.of_nat Pos.of_succ_nat]. clear - M M1 M2 M3 M4 M5; lia. }
    destruct (range_dec x (8 * sc + 614568) 8) as [C2|C2].
    { left. exists (usg_cell (Z.to_nat sc) (nth (Z.to_nat sc) (st_usage s6n) 0)). split; [unfold CnewN; left; reflexivity|].
      unfold in_rng, cell_range, usg_cell. cbn [mc_loc mc_w fst snd]. rewrite Lc. unfold CTX_usage. rewrite Z2Nat.id by lia. cbn [Z.of_nat Pos.of_succ_nat]. clear - C2; lia. }
    destruct (range_dec x (8 * sc + 614184) 8) as [C3|C3].
    { left. exists (act_cell (Z.to_nat sc) (Some mt)). split; [unfold CnewN; right; left; reflexivity|].
      unfold in_rng, cell_range, act_cell. cbn [mc_loc mc_w fst snd]. rewrite Lc. unfold CTX_active. rewrite Z2Nat.id by lia. cbn [Z.of_nat Pos.of_succ_nat]. clear - C3; lia. }
    destruct (range_dec x (st - 3) 3) as [H3|H3].
    { left. destruct (Z.eq_dec x (st - 3)) as [E3|E3].
      - eexists. split; [apply INH; unfold hdr_cells; left; reflexivity|].
        unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd]. rewrite LS. cbn [Z.of_nat Pos.of_succ_nat]. clear - E3; lia.
      - eexists. split; [apply INH; unfold hdr_cells; right; left; reflexivity|].
        unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd]. rewrite LS. cbn [Z.of_nat Pos.of_succ_nat]. clear - E3 H3; lia. }
    destruct (range_dec x st 9) as [W1|W1].
    { left. destruct (range_dec x st 8) as [G0|G0].
      - eexists. split; [apply ING; unfold group_cells; left; reflexivity|].
        unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd am_mem am_set_links new_am]. rewrite LS. cbn [Z.of_nat Pos.of_succ_nat]. clear - G0; lia.
      - eexists. split; [apply ING; unfold group_cells; cbn [am_maplen am_set_links new_am Z.eqb]; right; left; reflexivity|].
        unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd am_mem am_set_links new_am]. rewrite loc_padd, LS. cbn [Z.of_nat Pos.of_succ_nat]. clear - W1 G0; lia. }
    (* [comment removed for export] *)
    set (kk := (x - (st + 12)) / class_size sc).
    destruct (Z.eq_dec x (st + 12 + class_size sc * kk)) as [Ek|Ek].
    2:{ exfalso. apply Hne. apply (nn_out m4 idx memv st mta sc cnt0 (usage_of s4 sc) hb Hsc Hcnt Hsize Hst Hend Pm1 Hmta47 Pm3 Dst Dms x Hx).
        intros [A|[A|[A|[A|[A|(k & Hk & A)]]]]]; [clear - A M; lia | clear - A C2; lia | clear - A C3; lia | clear - A H3; lia | clear - A W1; lia |].
        apply Ek. unfold kk. rewrite A. replace (st + 12 + class_size sc * k - (st + 12)) with (k * class_size sc) by ring.
        rewrite Z.div_mul by lia. ring. }
    destruct (Z_le_gt_dec 0 kk) as [K0|K0].
    2:{ exfalso. apply Hne. apply (nn_out m4 idx memv st mta sc cnt0 (usage_of s4 sc) hb Hsc Hcnt Hsize Hst Hend Pm1 Hmta47 Pm3 Dst Dms x Hx).
        intros [A|[A|[A|[A|[A|(k & Hk & A)]]]]]; [clear - A M; lia | clear - A C2; lia | clear - A C3; lia | clear - A H3; lia | clear - A W1; lia |].
        rewrite Ek in A. assert (kk = k) by (clear - A Hsize; nia). lia. }
    destruct (Z_le_gt_dec kk cnt0) as [K1|K1].
    2:{ exfalso. apply Hne. apply (nn_out m4 idx memv st mta sc cnt0 (usage_of s4 sc) hb Hsc Hcnt Hsize Hst Hend Pm1 Hmta47 Pm3 Dst Dms x Hx).
        intros [A|[A|[A|[A|[A|(k & Hk & A)]]]]]; [clear - A M; lia | clear - A C2; lia | clear - A C3; lia | clear - A H3; lia | clear - A W1; lia |].
        rewrite Ek in A. assert (kk = k) by (clear - A Hsize; nia). lia. }
    destruct (Z_lt_le_dec kk cnt0) as [K2|K2].
    { assert (Hsize_st : stride_of (am_set_links (Some mt) (Some mt) (new_am p sc cnt0 (cnt0 - 1) 0 slot_junk)) = class_size sc).
      { unfold stride_of. cbn [am_last am_sc am_maplen am_set_links new_am]. replace (0 =? 0) with true by reflexivity. cbn [negb andb].
        destruct (cnt0 - 1 =? 0); reflexivity. }
      left. eexists. split.
      - apply ING. unfold group_cells. apply in_app_iff. right. apply in_flat_map. exists kk. split; [apply In_zseq; cbn [am_last am_set_links new_am]; lia|].
        unfold slot_cells. assert (Hsl : nth_slot (am_set_links (Some mt) (Some mt) (new_am p sc cnt0 (cnt0 - 1) 0 slot_junk)) kk = slot_junk).
        { unfold nth_slot. cbn [am_slots am_set_links new_am]. rewrite nth_repeat'. destruct (Nat.ltb (Z.to_nat kk) (Z.to_nat cnt0)); reflexivity. }
        rewrite Hsl. cbn [ss_hdr ss_fr slot_junk app]. left. reflexivity.
      - unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd]. rewrite loc_padd.
        assert (E1 : slot_start (am_set_links (Some mt) (Some mt) (new_am p sc cnt0 (cnt0 - 1) 0 slot_junk)) kk = padd p (UNIT + class_size sc * kk)).
        { unfold slot_start at 1. rewrite Hsize_st. reflexivity. }
        rewrite E1, !loc_padd. unfold UNIT. cbn [Z.of_nat Pos.of_succ_nat]. rewrite Ek. clear. lia. }
    assert (Ekc : kk = cnt0) by lia. rewrite Ekc in Ek.
    destruct (Z_lt_le_dec x (st + stride_of amg - 4) ) as [Lt|Ge].
    { right. split; [exact Ek | exact Lt]. }
    (* [comment removed for export] *)
    exfalso. apply Hne.
    assert (Exe : x = st + stride_of amg - 4) by (rewrite Ek; clear - Ge Hnest Ek; lia).
    rewrite Ek at 1. rewrite (RZ cnt0 ltac:(lia)).
    assert (Hh : x < 0x10000 \/ 0x97000 <= x) by (rewrite Exe, Est; clear - G4 Hgx Hnest Hspan Ho Sp Hidx; nia).
    assert (Hx' : 0 <= x < 2^64) by exact Hx.
    symmetry. destruct (Z_lt_le_dec idx (am_last amg)) as [Li|Li].
    + (* [comment removed for export] *)
      assert (Hc : In (MCell (LMem (padd (slot_start amg (idx + 1)) (-4))) 1 (VZ 0)) (image s4)).
      { unfold image. apply in_app_iff. right. apply in_app_iff. right. apply in_flat_map. exists (g, amg). split; [exact (used_g_s4 g amg s4 Mg)|].
        cbn [fst snd]. unfold group_cells. apply in_app_iff. right. apply in_flat_map. exists (idx + 1). split; [apply In_zseq; lia|].
        unfold slot_cells. left. reflexivity. }
      pose proof (repr_x_holds L s4 (bview SEGS m4) [] _ (nc_repr _ _ _ _ _ _ _ N) Hc (fun H => H)) as HH.
      assert (Ea : loc_addr L (LMem (padd (slot_start amg (idx + 1)) (-4))) = x).
      { rewrite Exe, Est, loc_padd. unfold slot_start. rewrite !loc_padd. destruct (am_mem amg) as [rr oo]. cbn [loc_addr prid poff]. unfold UNIT. ring. }
      rewrite <- Ea. apply holds_zero_byte; [exact HH | rewrite Ea; exact Hx' | rewrite Ea; exact Hh].
    + (* [comment removed for export] *)
      assert (Eli : idx = am_last amg) by lia.
      assert (Hc : In (gend_cell amg) (markers s4)).
      { unfold markers. apply in_flat_map. exists (g, amg). split; [exact (used_g_s4 g amg s4 Mg)|]. cbn [snd]. unfold meta_markers. apply in_app_iff. right. left. reflexivity. }
      pose proof (proj1 (Forall_forall _ _) MK4 _ Hc) as HH.
      assert (Ea : loc_addr L (mc_loc (gend_cell amg)) = x).
      { rewrite Exe. cbn [gend_cell mc_loc]. unfold slot_end. rewrite loc_padd. rewrite <- Eli. unfold IB. ring. }
      unfold gend_cell in HH, Ea. cbn [mc_loc] in Ea. rewrite <- Ea. apply holds_zero_byte; [exact HH | rewrite Ea; exact Hx' | rewrite Ea; exact Hh].
Qed.
End CUTN.


