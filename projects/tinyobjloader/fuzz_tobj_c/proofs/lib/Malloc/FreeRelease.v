(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "or"; "iff"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "sub"; "mul"; "pow"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "frame"; "mslot"; "nth_slot"; "MUsed"; "fr_off"; "am_last"; "slot_start"; "IB"; "am_mem"; "am_sc"; "ameta"; "astate"; "region"; "ss_fr"; "UNIT"; "am_freed"; "am_next"; "am_prev"; "stride_of"; "FUser"; "am_aidx"; "am_avail"; "am_maplen"; "fkind"; "fr_kind"; "fr_n"; "padd"; "slotst"; "IRet"; "NEST_FUEL"; "RkMap"; "SP"; "itree"; "mkSlot"; "prid"; "release_slot"; "rg_kind"; "rg_len"; "rg_live"; "rkind"; "ss_hdr"; "st_areas"; "@Corelib.Init.Datatypes"; "Some"; "pair"; "option"; "prod"; "bool"; "nil"; "list"; "app"; "true"; "None"; "cons"; "unit"; "tt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "image"; "cell_range"; "group_extent"; "usedX"; "LMem"; "MT"; "footprint"; "frame_ptr"; "loc"; "MCell"; "U0"; "VZ"; "alloc_owned"; "bounded"; "group_cells"; "layout_ok"; "meta_bits"; "meta_slot_cells"; "ranges_disjoint"; "slot_cells"; "used_metas"; "CTX_SIZE"; "Inv"; "active_hd"; "area_cells"; "crange"; "ctx_cells"; "range_incl"; "region_of"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeRelease.RelMeta"; "am1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeRelease.RelModel"; "rs1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeRelease.RelGap"; "gzp"; "ravoid"; "gn"; "gzm"; "H16'"; "H3'"; "gst"; "rnewc"; "rtouched"; "rbv0"; "rnew"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeRelease"; "am1"; "rs1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "wz"; "addr_of"; "blocks"; "vm_ok"; "byteview_of"; "mc_chk_guard"; "mc_chk_guard_got"; "mc_ctx"; "mc_ctz_tab"; "mc_errno"; "mc_libc"; "mc_lock"; "mc_med_cnt_tab"; "mc_replaced"; "mc_size_classes"; "mc_small_cnt_tab"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel"; "frame_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "reprO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones"; "zone_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "MInv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "ublist"; "upd_meta"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier"; "reach_ok"; "@Corelib.Init.Peano"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree"; "fneed"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocLemmasRing MallocWfInv MallocWfFrame MallocWfSurgery MallocWfGeom MallocWfRepr MallocWfMain
  MallocWfSlot MallocWfFree MallocLayout MallocFooter MallocFooterLemmas MallocIface MallocIfaceI MallocLaws
  Zones Zones2 ImageUpd FreeQuickModel FreeQuickPost GapShrink NestTier TryAvailPost.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section RelMeta.
  Variables (s : astate) (g : sptr) (am : ameta) (i : Z) (fr : frame).
  Hypothesis HW : WF s.
  Hypothesis FFx : ltac2:(tb__ "0|0|
S87Vs;Vg;Vam;Vi;Vfr;A5").

  Definition am1 : ameta := release_slot_am am i.

  Lemma am1_fields : ltac2:(tb__ "0|1|
S1S0S3bSeA1M0S20S65A1S20Vam;A1A3S1S0G0S1fS65A1S1fVam;A1A3S1S0SeS17S65A1S17Vam;A1A3S1S0S6S24S65A1S24Vam;A1A3S1S0S6S1eS65A1S1eVam;A1A3S1S0S6S14S65A1S14Vam;A1A3S1S0S6S18S65A1S18Vam;A1A3S1S0S6S25S65A1S25Vam;A1A3S0S6S23S65A1S23Vam;A1A3A2A2A2A2A2A2A2A2").
  Proof using . repeat split; reflexivity. Qed.
  Lemma am1_stride : ltac2:(tb__ "0|0|
S0S6S21S65A1S21Vam;A1A3"). Proof using . reflexivity. Qed.
  Lemma am1_slot_start j : ltac2:(tb__ "0|0|
S0SeS15S65Vj;A2S15Vam;Vj;A2A3"). Proof using . reflexivity. Qed.
  Lemma am1_extent : ltac2:(tb__ "0|0|
S0S6S49S65A1S49Vam;A1A3"). Proof using . reflexivity. Qed.
  Lemma am1_bits : ltac2:(tb__ "0|0|
S0S6S57S65A1S57Vam;A1A3"). Proof using . reflexivity. Qed.
  Lemma am1_meta_cells : ltac2:(tb__ "0|0|
S0S3fS46A1S58Vg;S39S10S12S65A1A2A2S58Vg;S39S10S12Vam;A1A2A2A3").
  Proof using . reflexivity. Qed.

  Lemma am1_nth_slot j : ltac2:(tb__ "0|2|
S7Z0M0Vj;A2S0S2aS11S65Vj;A2S3dS2aL_;SdVj;Vi;A2S30S3dS3bS3cS6S6A2M1A1L_;SdS13Vfr;A1G0A2S39G1S3aS6S6ZffG0A4A2S37S11Vam;Vi;A2A1X3dx2S42SfA1A2S11Vam;Vj;A2X3dx2A3F_;").
  Proof using FFx HW.
    intros Hj. pose proof (ff_i _ _ _ _ _ FFx) as Hi. pose proof (ff_slot _ _ _ _ _ FFx) as Hsl.
    pose proof (ff_used _ _ _ _ _ FFx) as Hu.
    unfold am1, release_slot_am, upd_slot, nth_slot. cbn [am_slots am_set_slots].
    rewrite nth_lupd.
    assert (Hlen : length (am_slots am) = Z.to_nat (am_last am + 1)).
    { pose proof (inv_groups HW g am Hu) as ((_ & _ & L & _) & _). exact L. }
    destruct (j =? i) eqn:E.
    - apply Z.eqb_eq in E. subst j. rewrite Nat.eqb_refl.
      replace (Nat.ltb (Z.to_nat i) (length (am_slots am))) with true by (symmetry; apply Nat.ltb_lt; rewrite Hlen; lia).
      cbn [andb]. unfold released_slot, nth_slot. unfold nth_slot in Hsl. rewrite Hsl. destruct (fr_off fr =? 0); reflexivity.
    - apply Z.eqb_neq in E. replace (Nat.eqb (Z.to_nat j) (Z.to_nat i)) with false by (symmetry; apply Nat.eqb_neq; lia).
      reflexivity.
  Qed.

  Lemma am1_slot_cells j : ltac2:(tb__ "0|0|
S7Z0Vj;A2S2S0S6Vj;Vi;A3A1S0S3fS46A1S5aS65Vj;A2S5aVam;Vj;A2A3F_;F_;").
  Proof using FFx HW.
    intros Hj Hne. unfold slot_cells. rewrite (am1_nth_slot j Hj). replace (j =? i) with false by (symmetry; apply Z.eqb_neq; exact Hne).
    reflexivity.
  Qed.
End RelMeta.

Section RelModel.
  Variables (s : astate) (g : sptr) (am : ameta) (i : Z) (fr : frame).
  Hypothesis HW : WF s.
  Hypothesis FFx : ltac2:(tb__ "0|0|
S87Vs;Vg;Vam;Vi;Vfr;A5").
  Hypothesis Hkind : ltac2:(tb__ "0|0|
S0S26S27Vfr;A1S22A3").

  Definition rs1 : astate := ltac2:(tb__ "0|0|
S8eVg;S12S72Vam;Vi;A2A1Vs;A3").

  Lemma R_u : ltac2:(tb__ "0|0|
S4aS3eSeA1Vs;Vg;Vam;A4"). Proof using FFx. exact (ff_used _ _ _ _ _ FFx). Qed.
  Lemma R_MT : ltac2:(tb__ "0|0|
S0S3bS10A1S4cVs;Vg;A2S39S10S12Vam;A1A2A3"). Proof using FFx. exact (ff_MT _ _ _ _ _ FFx). Qed.
  Lemma R_i : ltac2:(tb__ "0|0|
S1S7Z0Vi;A2S7Vi;S14Vam;A1A2A2"). Proof using FFx. exact (ff_i _ _ _ _ _ FFx). Qed.
  Lemma R_sl : ltac2:(tb__ "0|0|
S0S3bSfA1S1cS11Vam;Vi;A2A1S39SfVfr;A2A3"). Proof using FFx. exact (ff_slot _ _ _ _ _ FFx). Qed.
  Lemma R_ND : List.NoDup (keys s). Proof using HW. exact (proj1 (inv_keys HW)). Qed.
  Lemma R_um : ltac2:(tb__ "0|0|
S64S3cSeS19A2S3aSeS19Vg;Vam;A4S5bVs;A1A3"). Proof using FFx HW. apply (used_metas_usedX s g am HW). exact R_u. Qed.

  Lemma release_slot_eq : ltac2:(tb__ "0|1|
S0S2fS1aS3cS44S1aA2M0A2S32Vg;Vi;Vs;A3S2bS1aG0S3aS44S1aS45S66A4A3A3").
  Proof using FFx.
    unfold release_slot. rewrite (bind_eq _ _ s am s (getm_eq s g am R_MT)). rewrite R_sl.
    rewrite setm_eq. unfold rs1, am1, release_slot_am, released_slot. rewrite R_sl. reflexivity.
  Qed.

  Lemma R_Inv1 : ltac2:(tb__ "0|0|
S5dS3eSeA1S39S3cSeS6A2S3aSeS6Vg;Vi;A4A2S51S66A4").
  Proof using FFx HW Hkind.
    assert (T : itok (release_slot g i s) (fun r => Inv [] (Some (g, i)) U0 (snd r))).
    { apply (release_slot_spec [] U0 s g i am fr (fun r => Inv [] (Some (g, i)) U0 (snd r)) HW R_u R_i R_sl Hkind). intros s' x -> Hx HI'. exact HI'. }
    rewrite release_slot_eq in T. exact T.
  Qed.
  Lemma R_MT1 : ltac2:(tb__ "0|0|
S0S3bS10A1S4cS66Vg;A2S39S10S12S72Vam;Vi;A2A1A2A3"). Proof using . unfold rs1. apply MT_upd_same. Qed.
  Lemma R_u1 : ltac2:(tb__ "0|0|
S4aS3eSeA1S66Vg;S72Vam;Vi;A2A4"). Proof using . apply usedX_intro; [reflexivity | exact R_MT1]. Qed.
  Lemma R_sl1 : ltac2:(tb__ "0|0|
S0S3bSfA1S1cS11S72Vam;Vi;A2Vi;A2A1S42SfA1A3").
  Proof using FFx HW. rewrite (am1_nth_slot s g am i fr HW FFx i) by (pose proof R_i; lia). rewrite Z.eqb_refl. reflexivity. Qed.
  Lemma R_layout L : ltac2:(tb__ "0|0|
S56VL;Vs;A2S56VL;S66A2F_;"). Proof using . intros H. exact H. Qed.
  Lemma R_footprint : ltac2:(tb__ "0|0|
S0S3fS3cS4fS6A2A1S4dS66A1S4dVs;A1A3"). Proof using . reflexivity. Qed.
  Lemma R_bounded : ltac2:(tb__ "0|0|
S54Vs;A1S54S66A1F_;"). Proof using . intros H. exact H. Qed.
  Lemma R_reach : ltac2:(tb__ "0|0|
S8fVs;A1S8fS66A1F_;").
  Proof using FFx. intros H. unfold rs1. apply (reach_ok_upd s g am (am1 am i) R_MT); [reflexivity | cbn; lia | exact H]. Qed.

  Lemma R_ring : ltac2:(tb__ "0|3|
S2S0S3cS3bSeA1M0G0A2S3aG0G0S20S72Vam;Vi;A2M1A1S1fG1A1A4S3aG0G0S42SeA1M2G2A4A3A1S2S0G0S5eS66S18G1A1A2S39SeVg;A2A3A1S2S0S6S1eG1A1Z0A3A1F_;F_;").
  Proof using FFx HW.
    cbn [am_prev am_next am_sc am_freed am1 release_slot_am upd_slot am_set_slots].
    replace (active_hd rs1 (am_sc am)) with (active_hd s (am_sc am)) by reflexivity.
    pose proof (ring_facts [] None U0 s g am HW R_u) as RF.
    pose proof (inv_groups HW g am R_u) as (_ & _ & _ & Gcl & _).
    intros HL Hnh. destruct Gcl as [(H63 & _) | (Hsc & _)].
    - exfalso. destruct (inv_rings HW) as (_ & _ & D). destruct (D g am R_u H63) as [P N]. apply HL.
      change (am_prev (upd_slot am i (released_slot am i))) with (am_prev am). change (am_next (upd_slot am i (released_slot am i))) with (am_next am).
      rewrite P, N. reflexivity.
    - destruct (RF ltac:(lia) ltac:(lia)) as (_ & _ & RF3). apply RF3; [exact HL | exact Hnh | intros; discriminate].
  Qed.
  Lemma R_fneed : ltac2:(tb__ "0|0|
S90S92S18S72Vam;Vi;A2A1A1S2cA2").
  Proof using FFx HW. cbn [am_sc am1 release_slot_am upd_slot am_set_slots]. apply fneed_le. pose proof (inv_groups HW g am R_u) as (_ & _ & _ & Gcl & _). destruct Gcl as [(H & _)|(H & _)]; lia. Qed.

  Lemma R_ublist : ltac2:(tb__ "0|3|
S3S3fS3cS3cSeS6A2M0G0A2M1A1M2G2S3G2G2S1S0G2S8dVs;A1S40G1R2S43G1S3aG0G0S3aSeS6S4eVam;Vi;Vfr;A3S28Vfr;A1A4S3aSeS6Vg;Vi;A4A4R1A3A3A3S0G2S8dS66A1S40G1R2R1A3A3A2Ll2;A2Ll1;A2").
  Proof using FFx HW Hkind.
    pose proof (inv_groups HW g am R_u) as ((_ & _ & Glen & _) & _).
    destruct (ublist_upd_slot s g am i (released_slot am i) R_ND R_MT R_i Glen) as (l1 & l2 & E1 & E2).
    exists l1, l2. unfold rs1, am1, release_slot_am. rewrite E2, E1. unfold slot_block, slotst_block. rewrite R_sl, Hkind.
    unfold released_slot. rewrite R_sl. destruct (fr_off fr =? 0); cbn; split; reflexivity.
  Qed.
  Lemma R_blocks L : ltac2:(tb__ "0|2|
S3S3fS3cS6S6A2M0A1M1G1S3G1G1S1S0G1S76VL;Vs;A2S40G0R2S43G0S3aS6S6S75VL;S4eVam;Vi;Vfr;A3A2S28Vfr;A1A4R1A3A3A3S0G1S76VL;S66A2S40G0R2R1A3A3A2Ll2;A2Ll1;A2").
  Proof using FFx HW Hkind.
    destruct R_ublist as (l1 & l2 & E1 & E2). unfold blocks.
    rewrite (user_blocks_ublist s R_ND), (user_blocks_ublist rs1 (proj1 (inv_keys R_Inv1))), E1, E2, !map_app, !map_map. cbn [map fst].
    exists (map (fun x => (addr_of L (fst (fst x)), snd (fst x))) l1), (map (fun x => (addr_of L (fst (fst x)), snd (fst x))) l2). split; reflexivity.
  Qed.
End RelModel.

Section RelGap.
  Variables (C : mconsts) (s : astate) (L : layout) (g : sptr) (am : ameta) (i : Z) (fr : frame).
  Variables (rd0 rd1 : word -> option byte) (wok0 wok1 : word -> bool) (vm : VmMaps).
  Hypothesis HMI : ltac2:(tb__ "0|0|
S8cVC;S8bVs;VL;A2Vrd0;Vwok0;Vvm;A5").
  Hypothesis FFx : ltac2:(tb__ "0|0|
S87Vs;Vg;Vam;Vi;Vfr;A5").
  Hypothesis Hkind : fr_kind fr = FUser.
  Hypothesis HS : statics_in_image C.
  Hypothesis HSD : ltac2:(tb__ "0|d|
S6S4S1S7S7bVC;A1M0R1A2S9R1S8G0S5cA2A2A2S1S7S7dVC;A1M1R1A2S9R1S8G1Z4M2A2A2A2A2S1S2S1S7S7eVC;A1M3R2A2S9R2S8G3Z38A2A2A2A1S1S2S1S7S81VC;A1M4R2A2S9R2S8G4G2A2A2A2A1S1S2S1S7S7fVC;A1M5R2A2S9R2S8G5G2A2A2A2A1S1S2S1S7S82VC;A1M6R2A2S9R2S8G6Z60A2A2A2A1S1S2S1S7S83VC;A1M7R2A2S9R2S8G7Z1bA2A2A2A1S1S2S1S7S80VC;A1M8R2A2S9R2S8G8G2A2A2A2A1S1S2S1S7S7cVC;A1M9R2A2S9R2S8G9Z20A2A2A2A1S1S2S1S7S7aVC;A1MaR2A2S9R2S8GaZ8MbA2A2A2A1S2S1S7S79VC;A1McR2A2S9R2S8GcGbA2A2A2A1A2A2A2A2A2A2A2A2F_;Fx;").

  Definition gp : sptr := ltac2:(tb__ "0|0|
S4eVam;Vi;Vfr;A3").
  Definition gn : Z := fr_n fr.
  Definition gzp : Z := addr_of L gp.
  Definition gst : Z := ltac2:(tb__ "0|0|
S75VL;S15Vam;Vi;A2A2").
  Definition gzm : Z := ltac2:(tb__ "0|0|
S75VL;S17Vam;A1A2").
  Let s1 : astate := ltac2:(tb__ "0|0|
S73Vs;Vg;Vam;Vi;A4").
  Let a1 : ameta := am1 am i.

  Definition rbv0 : byteview := byteview_of rd0 wok0.
  Definition rbv1 : byteview := byteview_of rd1 wok1.

  Definition rtouched (x : Z) : Prop := ltac2:(tb__ "0|0|
S1S7SaS67Z3A2Vx;A2S9Vx;S67A2A2").
  Definition rnew (x : Z) : Z := if x =? gzp - 3 then 255 else 0.
  Hypothesis V1 : ltac2:(tb__ "0|1|
S6S1S7Z0R1A2S9R1ScZ2Z40A2A2A2S2S6fR2A1A1S1S0S3bS84Q8A1A1Vrd1;S74R3A1M0A1Vrd0;G0A1A3S0S3dVwok1;G0A1Vwok0;G0A1A3A2F_;F_;Fx;").
  Hypothesis V3 : ltac2:(tb__ "0|3|
S6S6fR1A1S1S0S3dVwok1;S74R2A1M0A1S41A3S0S3bS84Q8M1A1M2A1Vrd1;G0A1S39G2S85G1S71R2A1A2A2A3A2F_;Fx;").
  Hypothesis VB : ltac2:(tb__ "0|1|
S6S1S7S67R1A2S9R1S8S67S69A2A2A2S1S0S3dVwok0;S74R2A1A1S41A3S3S84Q8A1M0G0S0S3bG0A1Vrd0;S74R3A1A1S39G0R1A2A3Lb;A2A2F_;Fx;").

  Lemma G_W : WF s. Proof using HMI. exact (proj1 HMI). Qed.
  Lemma G_u : ltac2:(tb__ "0|0|
S4aS3eSeA1Vs;Vg;Vam;A4"). Proof using FFx. exact (ff_used _ _ _ _ _ FFx). Qed.
  Lemma G_um : ltac2:(tb__ "0|0|
S64S3cSeS19A2S3aSeS19Vg;Vam;A4S5bVs;A1A3"). Proof using FFx HMI. apply (used_metas_usedX s g am G_W). apply G_u. Qed.
  Lemma G_i : ltac2:(tb__ "0|0|
S1S7Z0Vi;A2S7Vi;S14Vam;A1A2A2"). Proof using FFx. exact (ff_i _ _ _ _ _ FFx). Qed.
  Lemma G_sl : ltac2:(tb__ "0|0|
S0S3bSfA1S1cS11Vam;Vi;A2A1S39SfVfr;A2A3"). Proof using FFx. exact (ff_slot _ _ _ _ _ FFx). Qed.
  Lemma G_MT : ltac2:(tb__ "0|0|
S0S3bS10A1S4cVs;Vg;A2S39S10S12Vam;A1A2A3"). Proof using FFx. exact (ff_MT _ _ _ _ _ FFx). Qed.
  Lemma G_ND : List.NoDup (keys s). Proof using HMI. exact (proj1 (inv_keys G_W)). Qed.
  Lemma G_repr : ltac2:(tb__ "0|0|
S89VL;Vs;S70A3"). Proof using HMI. exact (proj1 (proj2 (proj2 (proj2 HMI)))). Qed.
  Lemma G_L : layout_ok L s. Proof using HMI. exact (proj1 (proj1 G_repr)). Qed.
  Lemma G_Hng : ltac2:(tb__ "0|0|
SfS0S3bSfA1S1cS11Vam;Vi;A2A1S39SfR1A2A3S0S26S27R2A1S22A3F_;Ff;").
  Proof using FFx Hkind. intros f Hf. rewrite G_sl in Hf. injection Hf as <-. exact Hkind. Qed.

  Lemma G_geom : ltac2:(tb__ "0|9|
S1S7Z10S21Vam;A1M0A2S1S7Z0M1S13Vfr;A1M2A2S1S7G1S69A2S1S7S8SbS1dG2A2M3S69A2SaG0S16A2M4A2S1S0S6S6dS8S8S6aS1dA2SbG0Vi;A2M5A2A3S1S0S6S67S8S6dG3A2A3S1S0S3cS6S6A2S8aVL;Vam;Vi;A3S3aS6S6SaS6dZ3M6A2S8G4G6A2A4A3S1S9G1S6aA2S1S9S8S8S6aS49Vam;A1M7A2S16A2ScZ2Z3fA2A2S1S7G1G5A2S1S7S8G5G0A2SbG0S8S14Vam;A1Z1A2A2M8A2S0S6G7SaS8S1dG8A2S16A2A3A2A2A2A2A2A2A2A2A2A2A2").
  Proof using FFx HMI.
    pose proof (inv_groups G_W g am G_u) as G0. pose proof (stride_pos _ _ _ _ _ G0) as Sp.
    pose proof (ff_off _ _ _ _ _ FFx) as Ho. pose proof (ff_n _ _ _ _ _ FFx) as Hn. pose proof (ff_fit _ _ _ _ _ FFx) as Hfit.
    destruct (used_group_region [] None U0 s g am G_W G_u) as (rg & Hr & Hk & Hl & Ho0 & Hext & _).
    pose proof (footprint_region_In s _ _ Hr Hk Hl) as InR.
    pose proof G_L as (_ & _ & _ & POS). destruct (POS _ InR) as [P1 P2]. unfold crange, loc_addr in P1, P2. cbn [fst snd] in P1, P2.
    pose proof G_i as Hi.
    assert (E1 : gst = gzm + UNIT + stride_of am * i).
    { unfold gst, gzm, addr_of, loc_addr, slot_start. destruct (am_mem am); cbn [padd]. lia. }
    assert (E2 : gzp = gst + UNIT * fr_off fr).
    { unfold gzp, gst, gp, addr_of, loc_addr, frame_ptr, slot_start. destruct (am_mem am); cbn [padd]. lia. }
    assert (Hsi : 0 <= stride_of am * i /\ stride_of am * i + stride_of am <= stride_of am * (am_last am + 1)) by (split; nia).
    assert (Ezm : gzm = ly_reg L (prid (am_mem am)) + poff (am_mem am)) by (unfold gzm, addr_of, loc_addr; destruct (am_mem am); reflexivity).
    unfold gn. split; [exact Sp|]. split; [lia|]. split; [exact Hn|]. split; [exact Hfit|].
    split; [exact E1|]. split; [exact E2|].
    split; [unfold zone_range; rewrite E1; unfold gzm, addr_of; reflexivity|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | reflexivity].
  Qed.

  Definition H3' : mcell := ltac2:(tb__ "0|0|
S50S4bS29S15Vam;Vi;A2N3A2A1U1S52ZffA1A3").
  Definition H16' : mcell := ltac2:(tb__ "0|0|
S50S4bS29S15Vam;Vi;A2N2A2A1U2S52Z0A1A3").
  Definition rnewc (c : mcell) : Prop := ltac2:(tb__ "0|0|
S1S0S6S13Vfr;A1Z0A3S4S0S46Vc;S6cA3S0S46Vc;S6bA3A2A2").

  Lemma H3'_range : ltac2:(tb__ "0|0|
S0S6S13Vfr;A1Z0A3S0S3cS6S6A2S48VL;S6cA2S3aS6S6SaS67Z3A2Z1A4A3F_;").
  Proof using FFx HMI.
    intros E0. pose proof G_geom as (_ & _ & _ & _ & E1 & E2 & _). unfold cell_range, H3'. cbn [mc_loc mc_w].
    fold (addr_of L (padd (slot_start am i) (-3))). f_equal. rewrite E2, E0. unfold gst, addr_of, loc_addr. destruct (slot_start am i); cbn [padd]. lia.
  Qed.
  Lemma H16'_range : ltac2:(tb__ "0|1|
S0S6S13Vfr;A1Z0A3S0S3cS6S6A2S48VL;S6bA2S3aS6S6SaS67Z2M0A2G0A4A3F_;").
  Proof using FFx HMI.
    intros E0. pose proof G_geom as (_ & _ & _ & _ & E1 & E2 & _). unfold cell_range, H16'. cbn [mc_loc mc_w].
    fold (addr_of L (padd (slot_start am i) (-2))). f_equal. rewrite E2, E0. unfold gst, addr_of, loc_addr. destruct (slot_start am i); cbn [padd]. lia.
  Qed.
  Lemma H'_in : ltac2:(tb__ "0|1|
S0S6S13Vfr;A1Z0A3S1S64S46S6cS47Vs1;A1M0A3S64S46S6bG0A3A2F_;").
  Proof using FFx HMI.
    intros E0.
    assert (K : forall c, In c (slot_cells a1 i) -> In c (image s1)).
    { intros c Hc. apply (upd_image_group s g am a1 G_ND G_MT). apply (In_group_slot g a1 i); [exact G_i | exact Hc]. }
    unfold slot_cells in K. unfold a1 in K. rewrite (am1_nth_slot s g am i fr G_W FFx i) in K by (pose proof G_i; lia).
    rewrite Z.eqb_refl in K. replace (fr_off fr =? 0) with true in K by (symmetry; apply Z.eqb_eq; exact E0). cbn [ss_hdr ss_fr app] in K.
    split; apply K; cbn; auto.
  Qed.

  Definition ravoid (c : mcell) : Prop := ltac2:(tb__ "0|1|
S59S48VL;Vc;A2S3aS6S6SaS67Z3M0A2G0A4A2").

  Lemma zone_avoid c : ltac2:(tb__ "0|0|
S59S48VL;Vc;A2S8aVL;Vam;Vi;A3A2S68Vc;A1F_;").
  Proof using FFx HMI.
    intros D. pose proof G_geom as (Sp & Ho & Hn & Hfit & E1 & E2 & EZ & _). rewrite EZ in D.
    unfold ravoid, ranges_disjoint in *. cbn [fst snd] in *. unfold UNIT, IB in *. lia.
  Qed.

  Lemma own_cells c : ltac2:(tb__ "0|0|
S64S46Vc;S55Vg;Va1;A2A3S4S6eVc;A1S1S64S46Vc;S47Vs;A1A3S68Vc;A1A2A2F_;").
  Proof using FFx HMI.
    intros Hc. pose proof G_geom as (Sp & Ho & Hn & Hfit & E1 & E2 & EZ & Pm & Pe & Si1 & Si2 & Eext). pose proof G_i as Hi.
    assert (OLDg : forall c', In c' (group_cells g am) -> In c' (image s)) by (intros c' H'; exact (In_image_group s g am c' G_um H')).
    unfold group_cells in Hc. apply in_app_iff in Hc as [Hh|Hsl].
    -
      right. split; [apply OLDg; unfold group_cells; apply in_app_iff; left; exact Hh|].
      unfold ravoid, cell_range. destruct Hh as [<-|[<-|[]]]; cbn [mc_loc mc_w].
      + change (loc_addr L (LMem (am_mem a1))) with gzm. unfold ranges_disjoint. cbn [fst snd]. unfold UNIT in *. lia.
      + unfold aidx_cell. change (am_maplen a1) with (am_maplen am). change (am_mem a1) with (am_mem am). change (am_aidx a1) with (am_aidx am).
        destruct (am_maplen am =? 0); cbn [mc_loc mc_w]; fold (addr_of L (padd (am_mem am) 8)); unfold addr_of, loc_addr; unfold gzm, addr_of, loc_addr in E1;
          destruct (am_mem am); cbn [padd] in *; unfold ranges_disjoint; cbn [fst snd]; unfold UNIT in *; lia.
    - apply in_flat_map in Hsl as [k [Hk Hc]]. apply In_zseq in Hk. change (am_last a1) with (am_last am) in Hk.
      destruct (Z.eq_dec k i) as [->|Hki].
      +
        unfold slot_cells in Hc. unfold a1 in Hc. rewrite (am1_nth_slot s g am i fr G_W FFx i) in Hc by lia. rewrite Z.eqb_refl in Hc.
        cbn [ss_hdr ss_fr] in Hc. rewrite app_nil_r in Hc. change (slot_start (am1 am i) i) with (slot_start am i) in Hc.
        pose proof (slot_start_cells s g am i G_W G_um G_i) as [SC0 SC].
        apply in_app_iff in Hc as [Hc|Hc].
        * destruct Hc as [<-|[]]. right. split; [exact SC0|].
          unfold ravoid, cell_range. cbn [mc_loc mc_w]. fold (addr_of L (padd (slot_start am i) (-4))).
          unfold addr_of, loc_addr. unfold gst, addr_of, loc_addr in E2. destruct (slot_start am i); cbn [padd] in *. unfold ranges_disjoint. cbn [fst snd]. unfold UNIT in *. lia.
        * destruct (fr_off fr =? 0) eqn:E0.
          -- apply Z.eqb_eq in E0. left. split; [exact E0|]. destruct Hc as [<-|[<-|[]]]; [left|right]; reflexivity.
          -- apply Z.eqb_neq in E0. right. destruct (ss_hdr (nth_slot am i)) as [[h3 h16]|]; [|destruct Hc].
             destruct SC as [S1 S2].
             assert (RG : forall d w v, cell_range L (MCell (LMem (padd (slot_start am i) d)) w v) = (gst + d, Z.of_nat w)).
             { intros d w v. unfold cell_range, gst, addr_of, loc_addr. cbn [mc_loc mc_w]. destruct (slot_start am i); cbn [padd]. f_equal. lia. }
             destruct Hc as [<-|[<-|[]]]; (split; [assumption|]); unfold ravoid;
               [rewrite (RG (-3) 1%nat (VZ h3)) | rewrite (RG (-2) 2%nat (VZ h16))]; unfold ranges_disjoint; cbn [fst snd]; unfold UNIT in *; lia.
      +
        unfold a1 in Hc. rewrite (am1_slot_cells s g am i fr G_W FFx k) in Hc by lia. right. split.
        * apply OLDg. apply (In_group_slot g am k); [lia | exact Hc].
        * destruct (In_slot_cells [] None U0 s g am k c G_W G_u ltac:(lia) Hc) as (d & E & Lo & Hiw & _).
          destruct (other_slot_off s g am i G_W G_u G_i k ltac:(lia) Hki) as [X|X]; rewrite poff_slot_start in X;
            unfold ravoid, cell_range; rewrite E; cbn [mc_loc mc_w]; fold (addr_of L (padd (am_mem am) d)); unfold addr_of, loc_addr;
            unfold zone_lo, zone_hi in X; rewrite ?poff_slot_start in X; unfold gzm, addr_of, loc_addr in E1;
            destruct (am_mem am); cbn [padd prid poff] in *; unfold ranges_disjoint; cbn [fst snd]; unfold UNIT, IB in *; lia.
  Qed.

  Lemma zone_entry : ltac2:(tb__ "0|2|
S3S1bS1bS1S0S3bS1bA1S63Vs;S31S17Vam;A1A1M0A2S39S1bR1A2A3S1S0S36S33R1A1S2dA3S1S0S3dS35R1A1S41A3S1S64S3cS4fS6A2S3aS4fS6S4bS2eG0Z0A2A1S34R1A1A4M1S4dVs;A1A3S62S8aVL;Vam;Vi;A3S60VL;G1A2A2A2A2A2A2Lrg;A2").
  Proof using FFx HMI. exact (Zones.zone_entry s L g am i G_W G_u G_i). Qed.

  Lemma ctx_cell_zone c : ltac2:(tb__ "0|0|
S64S46Vc;S61Vs;A1A3S68Vc;A1F_;").
  Proof using FFx HMI.
    intros Hc. apply zone_avoid. destruct zone_entry as (rg & Hr & Hk & Hl & InR & ZI).
    destruct (In_ctx_cells s c Hc) as (off & E & Ho' & Hw).
    apply (other_entry_addr s L g am i G_W G_L G_u G_i (LCtx 0, CTX_SIZE) _ rg); [left; reflexivity | | exact Hr | exact Hk | exact Hl | discriminate].
    unfold cell_range, crange, range_incl, loc_addr. rewrite E. cbn [fst snd]. lia.
  Qed.

  Lemma area_cell_zone a next c : ltac2:(tb__ "0|0|
S64SeVa;S38Vs;A1A3S64S46Vc;S5fVs1;Va;Vnext;A3A3S68Vc;A1F_;F_;").
  Proof using FFx HMI.
    intros Ha Hc. apply zone_avoid. destruct zone_entry as (rg & Hr & Hk & Hl & InR & ZI).
    destruct (In_area_cells s1 a next c Hc) as (d & E & Hd & Hw).
    pose proof (inv_areas G_W) as (_ & A2 & _). destruct (A2 a Ha) as (ra & oa & rga & Ea & _ & Hoa & _).
    apply (other_entry_addr s L g am i G_W G_L G_u G_i (LMem a, PGSZ) _ rg); [| | exact Hr | exact Hk | exact Hl |].
    - right. apply in_app_iff. left. apply in_map_iff. exists a. auto.
    - unfold cell_range, crange, range_incl, loc_addr. rewrite E. destruct a as [r o]. cbn [fst snd padd]. lia.
    - rewrite Ea. intros E2. injection E2 as _ Eo _. unfold PGSZ in Hoa. lia.
  Qed.

  Lemma other_group_zone q aq c : ltac2:(tb__ "0|0|
S4aS3eSeA1Vs;Vq;Vaq;A4S2S0SeVq;Vg;A3A1S64S46Vc;S55Vq;Vaq;A2A3S68Vc;A1F_;F_;F_;").
  Proof using FFx HMI Hkind.
    intros Hq Hne Hc. apply zone_avoid. destruct zone_entry as (rg & Hr & Hk & Hl & InR & ZI).
    pose proof (Zgeom s g am i G_W G_u G_i) as (Sp & Ho & Ezlo & Ezhi & Hj0 & Hj1 & Eext).
    destruct (In_group_cells_span [] None U0 s q aq c G_W Hq Hc) as (d & E & Hd & Hw).
    destruct (Nat.eq_dec (prid (am_mem aq)) (prid (am_mem am))) as [Hsame | Hdiff].
    -
      assert (OFF : off_zone am i (padd (am_mem aq) d) (Z.of_nat (mc_w c)) -> ranges_disjoint (cell_range L c) (zone_range L am i)).
      { intros Hoz. unfold cell_range. rewrite E. apply (off_zone_addr L am i); [lia | exact Hoz | rewrite prid_padd; exact Hsame]. }
      apply OFF. intros _. rewrite poff_padd.
      destruct (other_group_cases s g am i G_W G_u G_i G_Hng q aq Hq Hne Hsame) as [D | [(j0 & Hj0r & Hj0ne & Lo & Hi) | (J & frJ & HJ & HfrJ & HkJ & OffJ & Lo & Hi)]].
      + destruct D; [left|right]; lia.
      + destruct (other_slot_off s g am i G_W G_u G_i j0 Hj0r Hj0ne) as [X|X]; [left|right]; unfold UNIT, IB in *; lia.
      + destruct (group_cells_vs_body [] None U0 s q aq J (zone_lo am i) (zone_hi am i) c G_W Hq HJ Hc ltac:(rewrite HfrJ, OffJ; lia) Hi) as (d' & E' & D).
        rewrite E in E'. injection E' as Ed. apply (f_equal poff) in Ed. rewrite !poff_padd in Ed. replace (poff (am_mem aq) + d) with (poff (am_mem aq) + d') by lia. exact D.
    - destruct (used_group_region [] None U0 s q aq G_W Hq) as (rg' & Hr' & Hkd' & Hl' & Ho2 & Hext' & _).
      apply (other_entry_addr s L g am i G_W G_L G_u G_i (LMem (SP (prid (am_mem aq)) 0), rg_len rg') _ rg);
        [apply footprint_region_In; assumption | | exact Hr | exact Hk | exact Hl | intros E2; injection E2; intros _ Ep; exact (Hdiff Ep)].
      unfold cell_range, crange, range_incl, loc_addr. rewrite E. destruct (am_mem aq) as [r o]. cbn [fst snd padd prid poff] in *. unfold IB in *. lia.
  Qed.

  Lemma rel_zone c : ltac2:(tb__ "0|0|
S64S46Vc;S47Vs1;A1A3S4S6eVc;A1S68Vc;A1A2F_;").
  Proof using FFx HMI Hkind.
    intros Hin. destruct (In_image_inv s1 c Hin) as [Hc | [(a & next & Ha & Hc) | (q & aq & Hq & Hc)]].
    - right. apply ctx_cell_zone. exact Hc.
    - right. apply (area_cell_zone a next); [exact Ha | exact Hc].
    - destruct (upd_used_metas_In s g am a1 G_ND G_MT q aq Hq) as [[-> ->] | [Hne Hold]].
      + destruct (own_cells c Hc) as [N | [_ A]]; [left; exact N | right; exact A].
      + right. apply (other_group_zone q aq); [apply (used_metas_usedX s q aq G_W); exact Hold | exact Hne | exact Hc].
  Qed.
  Lemma rel_old c : ltac2:(tb__ "0|0|
S64S46Vc;S47Vs1;A1A3S4S6eVc;A1S64S46Vc;S47Vs;A1A3A2F_;").
  Proof using FFx HMI.
    intros Hin. destruct (upd_image_In s g am a1 G_ND G_MT c Hin) as [Hold | [Hm | Hgr]].
    - right. exact Hold.
    - right. unfold a1 in Hm. rewrite (am1_meta_cells g am i) in Hm. exact (meta_cells_in_image s g am c G_W G_u Hm).
    - destruct (own_cells c Hgr) as [N | [O _]]; [left; exact N | right; exact O].
  Qed.

  Lemma footer'_old c : ltac2:(tb__ "0|0|
S64S46Vc;S88Vs1;A1A3S64S46Vc;S88Vs;A1A3F_;").
  Proof using FFx HMI a1.
    intros Hin. destruct (upd_footer_In s g am a1 G_ND G_MT c Hin) as [H|H]; [exact H|].
    unfold footer_cells. apply in_flat_map. exists (g, am). split; [exact G_um|]. cbn [snd].
    unfold group_footer_cells in *. destruct H as [<-|H]; [left; reflexivity|]. right.
    apply in_flat_map in H as [j [Hj H]]. apply In_zseq in Hj. change (am_last a1) with (am_last am) in Hj.
    unfold a1 in H. rewrite (am1_nth_slot s g am i fr G_W FFx j) in H by lia.
    destruct (j =? i) eqn:Eji; [destruct H|].
    apply in_flat_map. exists j. split; [apply In_zseq; lia|].
    destruct (ss_fr (nth_slot am j)) as [f|]; [|destruct H]. exact H.
  Qed.
  Lemma footer_zone c : ltac2:(tb__ "0|0|
S64S46Vc;S88Vs;A1A3S68Vc;A1F_;").
  Proof using FFx HMI Hkind VB.
    intros Hin. pose proof G_geom as (Sp & Ho & Hn & Hfit & E1 & E2 & EZ & _).
    destruct (zone_footer_addr s L g am i G_W G_L G_u G_i G_Hng c Hin) as [(f & Hf & Hc) | D]; [|exact (zone_avoid c D)].
    rewrite G_sl in Hf. injection Hf as <-.
    assert (Hr : 0 <= reserved_of am fr) by (unfold reserved_of; unfold gn in Hn, Hfit; lia).
    destruct (frame_footer_above_block am i fr c Sp (ff_n _ _ _ _ _ FFx) Hr Hc) as (d & E & Lo & Hi).
    unfold ravoid, cell_range. rewrite E. cbn [mc_loc mc_w]. unfold gzp, gp, addr_of, loc_addr in *.
    destruct (frame_ptr am i fr) as [r o]; cbn [padd] in *. unfold ranges_disjoint. cbn [fst snd]. unfold gn in *. lia.
  Qed.

  Lemma R_vm_ok : ltac2:(tb__ "0|0|
S5S77VL;Vs1;Vvm;A3S77VL;Vs;Vvm;A3A2"). Proof using am g i. unfold s1, rs1. split; intros H; exact H. Qed.

  Lemma touched_zone x : ltac2:(tb__ "0|0|
S6fVx;A1S3S6S6S1S1S7Z0R1A2S9R1S8S49Vam;A1S16A2A2A2S0S6Vx;S8S6aR1A2A3A2Ld;A2F_;").
  Proof using FFx HMI.
    intros T. pose proof G_geom as (Sp & Ho & Hn & Hfit & E1 & E2 & EZ & Pm & Pe & Si1 & Si2 & Eext). unfold rtouched in T.
    exists (x - gzm). unfold UNIT, IB in *. lia.
  Qed.

  Lemma R_own x : ltac2:(tb__ "0|0|
S53VL;Vs1;Vx;A3S4S53VL;Vs;Vx;A3S1S7S67Vx;A2S9Vx;S8S67S69A2A2A2A2F_;").
  Proof using FFx HMI Hkind.
    intros [(rg & Hrg & Hx) Hnu].
    pose proof (R_blocks s g am i fr G_W FFx Hkind L) as (l1 & l2 & BL0 & BL1). fold s1 in BL1.
    destruct (Z_le_dec gzp x) as [A|A]; [destruct (Z_lt_dec x (gzp + gn)) as [B|B]; [right; lia|]|]; left;
      (split; [exists rg; split; [exact Hrg | exact Hx]|]); intros (b & Hb & Hxb); apply Hnu;
      (assert (Hb' : In (addr_of L (fst b), snd b) (blocks L s)) by (unfold blocks; apply in_map_iff; exists b; auto));
      rewrite BL0 in Hb'; apply in_app_iff in Hb'; cbn [In] in Hb';
      (assert (CASE : In (addr_of L (fst b), snd b) (l1 ++ l2) \/ (gzp, gn) = (addr_of L (fst b), snd b)) by (clear - Hb'; rewrite in_app_iff; tauto));
      clear Hb'; (destruct CASE as [Hin | E]; [| exfalso; injection E as Eb En; unfold addr_of in Eb; rewrite <- Eb, <- En in Hxb; lia]);
      rewrite <- BL1 in Hin; unfold blocks in Hin; apply in_map_iff in Hin as [b2 [Eb2 Hb2]];
      exists b2; (split; [exact Hb2|]); injection Eb2 as E1 E2; unfold addr_of in E1; rewrite E1, E2; exact Hxb.
  Qed.

  Lemma bv_lit (rd : word -> option byte) (wok : word -> bool) x b : ltac2:(tb__ "0|3|
S1S7Z0Vx;A2S9Vx;ScZ2Z40A2A2A2S0S3dVwok;S74Vx;A1M0A1S41A3S0S3bS84Q8M1A1M2A1Vrd;G0A1S39G2Vb;A2A3S0S3bS6A1S78Vrd;Vwok;Vx;A3S39S6S86G1Vb;A2A2A3F_;F_;F_;").
  Proof using .
    intros Hx W R. unfold byteview_of. unfold wz in W, R.
    replace ((0 <=? x) && (x <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
    cbn [andb]. rewrite W, R. reflexivity.
  Qed.

  Theorem minv_release : ltac2:(tb__ "0|0|
S91VC;S3eSeA1S39S3cSeS6A2S3aSeS6Vg;Vi;A4A2S51S8bVs1;VL;A2Vrd1;Vwok1;Vvm;A8").
  Proof using FFx HMI HS HSD Hkind V1 V3 VB a1.
    pose proof G_geom as (Sp & Ho & Hn & Hfit & E1 & E2 & EZ & Pm & Pe & Si1 & Si2 & Eext). pose proof G_i as Hi.
    pose proof (proj1 (MInv_MInvI C (mkMA s L) rd0 wok0 vm) HMI) as [HMI0 HRO]. cbn [ma_s] in HRO.
    pose proof HMI as (_ & HB & HC & _ & HV & _). cbn [ma_s ma_L] in HB, HC, HV.
    pose proof (R_Inv1 s g am i fr G_W FFx Hkind) as HI1. fold s1 in HI1.
    assert (DECt : forall x, {rtouched x} + {~ rtouched x}) by (intros x; unfold rtouched; destruct (Z_le_dec (gzp - 3) x); [destruct (Z_lt_dec x gzp); [left; lia|] |]; right; lia).
    assert (RZP : 16 < gzp /\ gzp + gn + IB < 2 ^ 63) by (unfold UNIT, IB in *; lia).
    assert (NEWhold : fr_off fr = 0 -> cell_holds L (sg_bv1 rd1 wok1) H3' /\ cell_holds L (sg_bv1 rd1 wok1) H16').
    { intros E0. pose proof (f_equal fst (H3'_range E0)) as R3. pose proof (f_equal fst (H16'_range E0)) as R16.
      unfold cell_range, H3', H16' in R3, R16 |- *. cbn [mc_loc mc_w fst] in R3, R16. unfold cell_holds. cbn [mc_val mc_loc mc_w sval_num]. rewrite R3, R16.
      unfold sg_bv1. split; intros j Hj.
      - assert (j = 0%nat) as -> by lia. cbn [Z.of_nat]. rewrite Z.add_0_r. destruct (V3 (gzp - 3) ltac:(unfold rtouched; lia)) as [W R].
        rewrite (bv_lit rd1 wok1 (gzp - 3) _ ltac:(lia) W R). unfold rnew. rewrite Z.eqb_refl. reflexivity.
      - destruct (V3 (gzp - 2 + Z.of_nat j) ltac:(unfold rtouched; lia)) as [W R].
        rewrite (bv_lit rd1 wok1 (gzp - 2 + Z.of_nat j) _ ltac:(lia) W R). unfold rnew. replace (gzp - 2 + Z.of_nat j =? gzp - 3) with false by (symmetry; apply Z.eqb_neq; lia).
        unfold le_byte. rewrite (Z.mod_0_l (2 ^ (8 * Z.of_nat 2))), Z.shiftr_0_l by lia. reflexivity. }
    refine (minv_postS C (Inv [] None U0) (Inv [] (Some (g, i)) U0) s s1 L rd0 rd1 wok0 wok1 vm HMI0 HI1 HB G_L
              (fun x => gzp <= x < gzp + gn) R_own (proj2 R_vm_ok HV) rtouched DECt _ _ _ _ _ _ _ _ HS _ HSD _).
    -
      intros x Hx NT. destruct (V1 x Hx NT) as [Er Ew]. unfold sg_bv1, sg_bv0, sg_rv1, sg_rv0, byteview_of. unfold wz in Er, Ew. rewrite Er, Ew. split; reflexivity.
    -
      intros c Hin [k [Hk T]]. apply in_app_iff in Hin as [Hin|Hin].
      + destruct (rel_zone c Hin) as [[E0 [-> | ->]] | A]; [exact (proj1 (NEWhold E0)) | exact (proj2 (NEWhold E0)) |].
        exfalso. unfold ravoid, cell_range, ranges_disjoint, rtouched in *. cbn [fst snd] in A. lia.
      + exfalso. pose proof (footer_zone c (footer'_old c Hin)) as A. unfold ravoid, cell_range, ranges_disjoint, rtouched in *. cbn [fst snd] in A. lia.
    -
      intros x Hx T _. destruct (V3 x T) as [W R]. unfold sg_bv1. rewrite (bv_lit rd1 wok1 x _ Hx W R). discriminate.
    -
      intros x Hx NT B. destruct (VB x B) as [W [b R]]. unfold sg_bv0. rewrite (bv_lit rd0 wok0 x b Hx W R). discriminate.
    -
      intros c Hin NM. apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff.
      + destruct (rel_old c Hin) as [[E0 HE] | O]; [|left; exact O].
        exfalso. apply NM. exists 0%nat.
        pose proof (H3'_range E0) as R3. pose proof (H16'_range E0) as R16. unfold cell_range in R3, R16.
        destruct HE as [-> | ->]; cbn [mc_w mc_loc H3' H16'] in *; (split; [lia|]); unfold rtouched;
          [injection R3 as R3' | injection R16 as R16']; replace (Z.of_nat 0) with 0 by reflexivity; unfold loc_addr in *; lia.
      + right. exact (footer'_old c Hin).
    - intros c Hin. exact (Zones2.cell_spanI [] (Some (g, i)) U0 s1 L HI1 (xraw_nil _) G_L c Hin).
    - intros x Hx. exact (Zones2.owned_spanI s1 L G_L x Hx).
    - intros c Hin. exact (Zones2.cell_w_posI s1 c Hin).
    -
      intros x T Himg. exfalso. destruct (touched_zone x T) as (d & Hd & ->).
      pose proof (Zones2.group_range [] None U0 s L (proj1 HMI0) G_L C vm g am G_u HV (mig_ledger HMI0)) as (_ & _ & NG & _).
      fold gzm in NG. lia.
    - intros Hf. exfalso. change (st_init_done s1) with (st_init_done s) in Hf. rewrite (ff_init _ _ _ _ _ FFx) in Hf. discriminate Hf.
  Qed.
End RelGap.
