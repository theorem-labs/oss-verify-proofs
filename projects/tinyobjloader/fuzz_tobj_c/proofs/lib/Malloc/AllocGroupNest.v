(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupNest.NE"; "ne_s3"; "post"; "ne_am"; "ne_p"; "amN"; "ne_hdr"; "ne_new"; "@Corelib.Init.Datatypes"; "list"; "Some"; "bool"; "option"; "prod"; "app"; "None"; "length"; "nat"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "MT"; "LMem"; "loc"; "MCell"; "VZ"; "footprint"; "image"; "keys"; "user_blocks"; "LCtx"; "active_hd"; "ctx_cells"; "group_extent"; "meta_bits"; "CTX_active"; "CTX_usage"; "Inv"; "group_cells"; "mc_loc"; "mc_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "mslot"; "MUsed"; "padd"; "stride_of"; "am_last"; "frame"; "st_areas"; "st_avail_meta_area_count"; "st_avail_meta_areas"; "st_bounces"; "st_brk"; "st_free_meta_head"; "st_init_done"; "st_meta_alloc_shift"; "st_mmap_counter"; "st_regions"; "st_seq"; "st_unmap_seq"; "UNIT"; "nth_slot"; "slotst"; "sptr_eqb"; "FGroup"; "IB"; "am_aidx"; "am_avail"; "am_freed"; "am_maplen"; "am_mem"; "am_next"; "am_prev"; "am_sc"; "brkst"; "class_size"; "mkFrame"; "mkSlot"; "region"; "slot_junk"; "slot_start"; "st_active"; "st_usage"; "usage_of"; "META_SIZE"; "am_slots"; "ss_fr"; "upd_slot"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "mul"; "sub"; "div"; "eqb"; "of_nat"; "to_nat"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "group_footer_cells"; "trailing_cell"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "blocks_of"; "upd_meta"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupGrow"; "gg_amS"; "ig"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfInv MallocWfFrame MallocWfRepr MallocWfGroup MallocFooter MallocLayout
  ImageUpd ImageDelta FreeNtImage AllocGroupPost AllocGroupImage AllocGroupGrow Zones2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section NE.
  Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z).
  Variables (s2 : astate) (m g : sptr) (amg : ameta) (idx sc cnt0 j : Z) (xold : mslot).
  Hypothesis HI : ltac2:(tb__ "0|0|
S27VX;VR;VU;Vs2;A4").
  Hypothesis ND : NoDup (keys s2).
  Hypothesis Hm : ltac2:(tb__ "0|0|
S0SfS2cA1S17Vs2;Vm;A2SdS2cVxold;A2A3").
  Hypothesis Hold : not_used xold.
  Hypothesis Mg : ltac2:(tb__ "0|0|
S0SfS2cA1S17Vs2;Vg;A2SdS2cS2dVamg;A1A2A3").
  Hypothesis Hgm : g <> m.
  Hypothesis Hidx : ltac2:(tb__ "0|0|
S1S5bZ0Vidx;A2S5bVidx;S30Vamg;A1A2A2").
  Hypothesis Hslots : ltac2:(tb__ "0|0|
S0S14S13S40S57Vamg;A1A2S61S5aS30Vamg;A1Z1A2A1A3").
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hlen_act : length (st_active s2) = 48%nat.
  Hypothesis Hlen_usg : length (st_usage s2) = 48%nat.

  Definition ne_hdr : Z * Z := ltac2:(tb__ "0|0|
S15S4S4S5aVidx;Zc0A2S5eS5cS2fVamg;A1Vidx;A2S3eA2A4").
  Definition ne_am : ameta := ltac2:(tb__ "0|0|
S59Vamg;Vidx;S4fSdS10S4S4A2SaA2SdS31S4eZ0S5dS4dVj;A1S43A2S42A3A2A2A3").
  Definition ne_s3 : astate := ltac2:(tb__ "0|0|
S67Vg;S2dS7A1Vs2;A3").
  Definition ne_p : sptr := slot_start amg idx.
  Definition amN : ameta := ltac2:(tb__ "0|0|
S68Vm;S8Vsc;Vcnt0;S5dVcnt0;Z1A2Z0S51A7").
  Definition post : astate := ltac2:(tb__ "0|0|
S69S5Vm;S8Vsc;Vcnt0;S5dVcnt0;Z1A2Z0S51A8").

  Lemma ne_am_fields : ltac2:(tb__ "0|1|
S1S0S2bS48S7A1S48Vamg;A1A3S1S0S4S30S7A1S30Vamg;A1A3S1S0S4S4bS7A1S4bVamg;A1A3S1S0S4S47S7A1S47Vamg;A1A3S1S0S4S2fS7A1S2fVamg;A1A3S1S0S4S23S7A1S23Vamg;A1A3S1S4S0S2bS52S7R1A2S52Vamg;R1A2A3Fi;S1S0SfS2bA1M0S4aS7A1S4aVamg;A1A3S1S0G0S49S7A1S49Vamg;A1A3S1S0S4S45S7A1S45Vamg;A1A3S1S0S4S46S7A1S46Vamg;A1A3S1S0S4S44S7A1S44Vamg;A1A3S0S4S24S7A1S24Vamg;A1A3A2A2A2A2A2A2A2A2A2A2A2A2").
  Proof using Hidx Hslots Mg. unfold ne_am. pose proof (upd_slot_fields amg idx (mkSlot (Some ne_hdr) (Some (mkFrame 0 (class_size j - IB) FGroup)))) as F. destruct amg; repeat split; try reflexivity. Qed.
  Lemma ne_slot i : ltac2:(tb__ "0|1|
S5bZ0M0Vi;A2S0S40S3fS7Vi;A2SeS40L_;S5fVi;Vidx;A2S4fSdS10S4S4A2SaA2SdS31S4eG0S5dS4dVj;A1S43A2S42A3A2A2S3fVamg;Vi;A2Xex2A3F_;").
  Proof using Hidx Hlen_act Hlen_usg Hsc Hslots. intros Hi. unfold ne_am. apply nth_slot_upd_slot; [lia | lia | rewrite Hslots; lia]. Qed.

  Lemma ne3_keys : ltac2:(tb__ "0|0|
S0ScS2bA1S1eS5A1S1eVs2;A1A3").
  Proof using Mg. unfold ne_s3. apply keys_upd_In. eapply MT_Some_In_keys. exact Mg. Qed.
  Lemma ne3_ND : NoDup (keys ne_s3). Proof using Mg ND. rewrite ne3_keys. exact ND. Qed.
  Lemma ne3_MT q : ltac2:(tb__ "0|1|
S0SfS2cA1M0S17S5Vq;A2SeG0L_;S41Vq;Vg;A2SdS2cS2dS7A1A2S17Vs2;Vq;A2Xex2A3").
  Proof using . unfold ne_s3. destruct (sptr_eqb q g) eqn:E; [apply sptr_eqb_eq in E; subst; apply MT_upd_same | apply MT_upd_other; apply sptr_eqb_neq; exact E]. Qed.
  Lemma ne3_Mm : ltac2:(tb__ "0|0|
S0SfS2cA1S17S5Vm;A2SdS2cVxold;A2A3").
  Proof using Hgm Hm. rewrite ne3_MT. replace (sptr_eqb m g) with false by (symmetry; apply sptr_eqb_neq; auto). exact Hm. Qed.
  Lemma ne3_fields : ltac2:(tb__ "0|2|
S1S0ScS50A1S3bS5A1S3bVs2;A1A3S1S0ScS2bA1S32S5A1S32Vs2;A1A3S1S0S4cS36S5A1S36Vs2;A1A3S1S0SeS38S5A1S38Vs2;A1A3S1S0ScSfS2bA1M0A1S53S5A1S53Vs2;A1A3S1S0ScS4A1M1S54S5A1S54Vs2;A1A3S1S0S4S3aS5A1S3aVs2;A1A3S1S0S4S39S5A1S39Vs2;A1A3S1S0S4S33S5A1S33Vs2;A1A3S1S0S2bS34S5A1S34Vs2;A1A3S1S0S4S3cS5A1S3cVs2;A1A3S1S0G1S3dS5A1S3dVs2;A1A3S1S0G1S35S5A1S35Vs2;A1A3S0G0S37S5A1S37Vs2;A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2").
  Proof using . repeat split; reflexivity. Qed.
  Lemma ne3_footprint : ltac2:(tb__ "0|0|
S0ScS10S19S4A2A1S1cS5A1S1cVs2;A1A3"). Proof using . reflexivity. Qed.
  Lemma ne3_ctx_cells : ltac2:(tb__ "0|0|
S0ScS16A1S22S5A1S22Vs2;A1A3"). Proof using . reflexivity. Qed.

  Hypothesis Hfr0 : ltac2:(tb__ "0|0|
S0SfS31A1S58S3fVamg;Vidx;A2A1S12S31A1A3").
  Lemma ne_am_blocks : ltac2:(tb__ "0|1|
S0ScS10S10S2bS4A2M0G0A2A1S66Vg;S7A2S66Vg;Vamg;A2A3").
  Proof using Hfr0 Hidx Hlen_act Hlen_usg Hsc Hslots Mg.
    unfold MallocWfFrame.blocks_of. rewrite (proj1 (proj2 ne_am_fields)). apply flat_map_ext_In. intros i Hi. apply In_zseq in Hi.
    unfold slot_block. rewrite (ne_slot i) by lia. destruct (Z.eqb_spec i idx) as [->|NE].
    - cbn [ss_fr fr_kind]. rewrite Hfr0. reflexivity.
    - rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ne_am_fields)))))) i). reflexivity.
  Qed.
  Lemma ne3_user_blocks : ltac2:(tb__ "0|0|
S0ScS10S2bS4A2A1S1fS5A1S1fVs2;A1A3").
  Proof using Hfr0 Hidx Hlen_act Hlen_usg Hsc Hslots Mg ND.
    rewrite (user_blocks_ublist s2 ND), (user_blocks_ublist ne_s3 ne3_ND). f_equal. unfold ublist. rewrite ne3_keys.
    apply flat_map_ext_In. intros q Hq. rewrite ne3_MT. destruct (sptr_eqb q g) eqn:E; [|reflexivity].
    apply sptr_eqb_eq in E. subst q. rewrite Mg. cbn [ucontrib]. exact ne_am_blocks.
  Qed.

  Lemma post_keys : ltac2:(tb__ "0|0|
S0ScS2bA1S1eS6A1S1eVs2;A1A3").
  Proof using Hgm Hm Mg. unfold post. rewrite (ig_keys ne_s3 m ne_p sc cnt0 (cnt0 - 1) 0 slot_junk xold ne3_Mm). exact ne3_keys. Qed.
  Lemma post_MT q : ltac2:(tb__ "0|2|
S0SfS2cA1M0S17S6Vq;A2SeG0L_;M1S41Vq;Vm;A2SdS2cS2dS9A1A2G1S41Vq;Vg;A2SdS2cS2dS7A1A2S17Vs2;Vq;A2Xex2Xex2A3").
  Proof using . unfold post. rewrite (ig_MT ne_s3 m ne_p sc cnt0 (cnt0 - 1) 0 slot_junk q). fold amN. rewrite ne3_MT. reflexivity. Qed.
  Lemma post_footprint : ltac2:(tb__ "0|0|
S0ScS10S19S4A2A1S1cS6A1S1cVs2;A1A3"). Proof using . reflexivity. Qed.
  Lemma post_user_blocks : ltac2:(tb__ "0|0|
S0ScS10S2bS4A2A1S1fS6A1S1fVs2;A1A3").
  Proof using Hfr0 Hgm Hidx Hlen_act Hlen_usg Hm Hold Hsc Hslots Mg ND. unfold post. rewrite (ig_user_blocks ne_s3 m ne_p sc cnt0 (cnt0 - 1) 0 slot_junk xold eq_refl ne3_ND ne3_Mm Hold). exact ne3_user_blocks. Qed.
  Lemma post_usage_sc : ltac2:(tb__ "0|0|
S0S4S55S6Vsc;A2S5aS55Vs2;Vsc;A2Vcnt0;A2A3").
  Proof using Hlen_act Hlen_usg Hsc. unfold post. rewrite (ig_usage_sc ne_s3 m ne_p sc cnt0 (cnt0 - 1) 0 slot_junk Hsc Hlen_act Hlen_usg). reflexivity. Qed.
  Lemma post_active_hd c : ltac2:(tb__ "0|1|
S5bZ0Vc;A2S0SfS2bA1M0S21S6Vc;A2SeG0L_;S5fVc;Vsc;A2SdS2bVm;A2S21Vs2;Vc;A2Xex2A3F_;").
  Proof using Hlen_act Hlen_usg Hsc. intros Hc. unfold post. rewrite (ig_active_hd ne_s3 m ne_p sc cnt0 (cnt0 - 1) 0 slot_junk Hsc Hlen_act Hlen_usg c Hc). reflexivity. Qed.
  Lemma post_fields : ltac2:(tb__ "0|1|
S1S0ScS50A1S3bS6A1S3bVs2;A1A3S1S0ScS2bA1S32S6A1S32Vs2;A1A3S1S0S4cS36S6A1S36Vs2;A1A3S1S0SeS38S6A1S38Vs2;A1A3S1S0S4S39S6A1S39Vs2;A1A3S1S0S4S33S6A1S33Vs2;A1A3S1S0S2bS34S6A1S34Vs2;A1A3S1S0S4S3aS6A1S3aVs2;A1A3S1S0S4S3cS6A1S3cVs2;A1A3S1S0ScS4A1M0S3dS6A1S3dVs2;A1A3S1S0G0S35S6A1S35Vs2;A1A3S0SfS2bA1S37S6A1S37Vs2;A1A3A2A2A2A2A2A2A2A2A2A2A2").
  Proof using . repeat split; reflexivity. Qed.

  Definition ne_new (c : mcell) : Prop := ltac2:(tb__ "0|2|
S2S0S19S29Vc;A1M0S20S5aS26S5cZ8Vsc;A2M1A2A1A3S2S0S19G0S20S5aS25G1A2A1A3S2S3S4S4S1S0S19G0S18S2eVm;R1A2A1A3S1S5bZ0R1A2S5bS5aR1S60S2aVc;A1A1A2S56A2A2A2Ld;A2S2S0S16Vc;S1aS18S2eS8N3A2A1U1S1bS5aVidx;Zc0A2A1A3A3S2S0S16Vc;S1aS18S2eS8N2A2A1U2S1bS5eS5cS2fVamg;A1Vidx;A2S3eA2A1A3A3S2S62S16Vc;S28Vm;S9A2A3S0S16Vc;S65S9A1A3A2A2A2A2A2A2").

  Lemma ne3_image_In c : ltac2:(tb__ "0|0|
S62S16Vc;S1dS5A1A3S2S62S16Vc;S1dVs2;A1A3S2S0S16Vc;S1aS18S2eS8N3A2A1U1S1bS5aVidx;Zc0A2A1A3A3S0S16Vc;S1aS18S2eS8N2A2A1U2S1bS5eS5cS2fVamg;A1Vidx;A2S3eA2A1A3A3A2A2F_;").
  Proof using HI Hidx Hlen_act Hlen_usg Hsc Hslots Mg ND.
    intros Hin. destruct (upd_image_In s2 g amg ne_am ND Mg c Hin) as [H|[H|H]].
    - left. exact H.
    -
      left. pose proof ne_am_fields as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13).
      apply (meta_cells_in_imageI X R U s2 HI g c (MT_Some_In_keys s2 g _ Mg)). rewrite Mg.
      unfold meta_slot_cells in H |- *. rewrite F1, F8, F9, F10, F11, F13 in H. exact H.
    -
      pose proof ne_am_fields as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13).
      rewrite (group_cells_eq g ne_am) in H.
      destruct H as [<-|[<-|H]].
      + left. apply (In_image_group s2 g amg); [apply (proj2 (used_metas_iff s2 g amg ND) Mg)|]. rewrite group_cells_eq. left. rewrite F1. reflexivity.
      + left. apply (In_image_group s2 g amg); [apply (proj2 (used_metas_iff s2 g amg ND) Mg)|]. rewrite group_cells_eq. right; left.
        unfold ImageDelta.aidx_cell. rewrite F1, F4, F12. reflexivity.
      + apply in_flat_map in H as (i & Hi & Hc). rewrite F2 in Hi. apply In_zseq in Hi.
        unfold slot_cells in Hc. rewrite (F7 i), (ne_slot i) in Hc by lia.
        destruct (Z.eqb_spec i idx) as [->|NE].
        * cbn [ss_hdr ss_fr fr_off Z.eqb app] in Hc. fold ne_p in Hc.
          destruct Hc as [<-|[<-|[<-|[]]]].
          -- left. apply (In_image_group s2 g amg); [apply (proj2 (used_metas_iff s2 g amg ND) Mg)|]. rewrite group_cells_eq. right; right.
             apply in_flat_map. exists idx. split; [apply In_zseq; lia|]. unfold slot_cells. left. reflexivity.
          -- right; left. reflexivity.
          -- right; right. unfold ne_hdr. reflexivity.
        * left. apply (In_image_group s2 g amg); [apply (proj2 (used_metas_iff s2 g amg ND) Mg)|]. rewrite group_cells_eq. right; right.
          apply in_flat_map. exists i. split; [apply In_zseq; lia|]. unfold slot_cells.
          assert (EH : forall fr, hdr_byte3 ne_am i fr = hdr_byte3 amg i fr) by (intros fr; unfold hdr_byte3, rsv_code; rewrite F5; reflexivity).
          assert (EO : forall fr, hdr_off16 ne_am i fr = hdr_off16 amg i fr) by (intros fr; unfold hdr_off16; rewrite F5; reflexivity).
          destruct (ss_fr (nth_slot amg i)) as [fr|]; [rewrite (EH fr), (EO fr) in Hc|]; exact Hc.
  Qed.

  Lemma ne_am_footers : ltac2:(tb__ "0|0|
S0ScS16A1S64S7A1S64Vamg;A1A3").
  Proof using Hfr0 Hidx Hlen_act Hlen_usg Hsc Hslots Mg.
    pose proof ne_am_fields as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
    unfold group_footer_cells.
    assert (ET : trailing_cell ne_am = trailing_cell amg).
    { pose proof (trailing_is_last_end ne_am) as T1. pose proof (trailing_is_last_end amg) as T2. unfold trailing_cell. rewrite T1, T2. unfold slot_end. rewrite F2, F5, (F7 (am_last amg)). reflexivity. }
    rewrite ET. f_equal. rewrite F2. apply flat_map_ext_In. intros i Hi. apply In_zseq in Hi. rewrite (ne_slot i) by lia.
    destruct (Z.eqb_spec i idx) as [->|NE]; [cbn [ss_fr]; rewrite Hfr0; reflexivity|].
    destruct (ss_fr (nth_slot amg i)) as [fr|]; [|reflexivity].
    unfold frame_footer_cells, frame_ptr, slot_end, reserved_of. rewrite F5, !(F7 i). reflexivity.
  Qed.
  Lemma ne3_footer_In c : ltac2:(tb__ "0|0|
S62S16Vc;S63S5A1A3S62S16Vc;S63Vs2;A1A3F_;").
  Proof using Hfr0 Hidx Hlen_act Hlen_usg Hsc Hslots Mg ND.
    intros Hin. destruct (upd_footer_In s2 g amg ne_am ND Mg c Hin) as [H|H]; [exact H|].
    rewrite ne_am_footers in H. unfold footer_cells. apply in_flat_map. exists (g, amg). split; [apply (proj2 (used_metas_iff s2 g amg ND) Mg) | exact H].
  Qed.

  Theorem ne_image_In c : ltac2:(tb__ "0|0|
S62S16Vc;S11S16S1dS6A1S63S6A1A3A3S2S62S16Vc;S11S16S1dVs2;A1S63Vs2;A1A3A3SbVc;A1A2F_;").
  Proof using HI Hfr0 Hgm Hidx Hlen_act Hlen_usg Hm Hsc Hslots Mg ND.
    intros Hin. unfold ne_new. apply in_app_iff in Hin as [Hin|Hin].
    - destruct (ig_image_In ne_s3 m ne_p sc cnt0 (cnt0 - 1) 0 slot_junk xold ne3_ND ne3_Mm Hsc Hlen_act Hlen_usg c Hin) as [H|H].
      + destruct (ne3_image_In c H) as [H0|[H0|H0]]; [left; apply in_app_iff; left; exact H0 | right | right]; tauto.
      + right. unfold ig_new in H. fold amN in H. tauto.
    - destruct (ig_footer_In ne_s3 m ne_p sc cnt0 (cnt0 - 1) 0 slot_junk xold eq_refl ne3_ND ne3_Mm c Hin) as [H|H].
      + left. apply in_app_iff. right. exact (ne3_footer_In c H).
      + right. fold amN in H. tauto.
  Qed.
End NE.
