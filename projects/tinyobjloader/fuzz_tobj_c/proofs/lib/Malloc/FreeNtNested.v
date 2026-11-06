(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "mslot"; "am_sc"; "ameta"; "am_last"; "MUsed"; "MFree"; "am_mem"; "am_maplen"; "astate"; "am_aidx"; "am_next"; "frame"; "nth_slot"; "st_regions"; "am_set_links"; "am_freed"; "am_prev"; "bind"; "slot_start"; "am_avail"; "region"; "ss_fr"; "st_usage"; "stride_of"; "slotst"; "st_free_meta_head"; "FGroup"; "IRet"; "bit"; "fkind"; "fr_kind"; "itree"; "mkSlot"; "ones"; "ss_hdr"; "st_active"; "st_metas"; "HActive"; "M"; "activate_group"; "am_slots"; "dequeue"; "free_meta"; "get_head"; "links_of"; "massert"; "mlookup"; "mupdate"; "osptr_eqb"; "ret"; "upd_slot"; "usage_of"; "with_links"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "iff"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "Some"; "option"; "None"; "list"; "prod"; "cons"; "bool"; "unit"; "pair"; "false"; "app"; "nil"; "tt"; "fst"; "length"; "nat"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "MT"; "usedX"; "Inv"; "memb"; "keys"; "loc"; "mcell"; "active_hd"; "group_extent"; "flinks"; "group_cells"; "meta_bits"; "meta_slot_cells"; "slot_cells"; "user_blocks"; "CTX_usage"; "LCtx"; "contrib"; "ring_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtNested.FreeGroupNested"; "amP'"; "fgn_s2"; "fgn_s3v"; "fgn_s3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtNested.ForgetUpd"; "am_forget"; "@Stdlib.Lists.List"; "In"; "last"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "eqb"; "lor"; "ltb"; "mul"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtNested.FreeGroupNested.Finish"; "fgn_s5"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost"; "fgm_s1"; "dq_post"; "fgm_s2"; "nmask"; "shape_kept"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "upd_meta"; "ub_same"; "blocks_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree"; "corr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier"; "hosts_ok"; "reach_ok"; "tier"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta"; "delta"; "meta_locs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "group_footer_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase"; "itok"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage"; "deltaU"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocLemmasRing MallocWfArith MallocWfInv MallocWfFrame MallocWfRings
  MallocWfRingOps MallocWfSlot MallocWfSurgery MallocWfGroup MallocWfGeom MallocWfRepr MallocFooter MallocWfFree ImageUpd ImageDelta TryAvailPost NestTier Zones2 FreeNtPost FreeNtImage.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma itok_of_eq {A} (m : itree astate A) (Q : A -> Prop) r : ltac2:(tb__ "0|0|
S80VA;Vm;VQ;A3S36S20S9VA;A2Vm;S1cS9VA;Vr;A3A3VQ;Vr;A1F_;F_;").
Proof. intros H E. rewrite E in H. exact H. Qed.

Lemma mupdate_same l p x : ltac2:(tb__ "0|0|
S36S3dS1A1S2fVl;Vp;A2S3cS1Vx;A2A3S36S3fS40S0S1A2A1S30Vl;Vp;Vx;A3Vl;A3F_;").
Proof.
  induction l as [|[q y] t IH]; cbn; intros H; [discriminate|].
  destruct (sptr_eqb p q) eqn:E; [injection H as ->; reflexivity|]. rewrite (IH H). reflexivity.
Qed.
Lemma upd_meta_same g x t : ltac2:(tb__ "0|0|
S36S3dS1A1S4dVt;Vg;A2S3cS1Vx;A2A3S36S9S75Vg;Vx;Vt;A3Vt;A3F_;").
Proof. intros H. unfold upd_meta. rewrite (mupdate_same _ _ _ H). destruct t; reflexivity. Qed.

Section FreeRing.
  Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (t : astate).
  Hypothesis HI : ltac2:(tb__ "0|0|
S4fVX;VR;VU;Vt;A4").
  Lemma fr_last_in_cons {A} (l : list A) (d : A) : ltac2:(tb__ "0|0|
S65VA;S66VA;Vl;Vd;A3S41VA;Vd;Vl;A3A3").
  Proof using .
    revert d. induction l as [|x tl IH]; intros d; [left; reflexivity|].
    destruct tl as [|y t']; [right; left; reflexivity|].
    change (last (x :: y :: t') d) with (last (y :: t') d). pose proof (IH d) as H. destruct H as [H|H]; [left; exact H | right; right; exact H].
  Qed.
  Lemma fr_last_hd_in {A} (m0 : A) rest : ltac2:(tb__ "0|1|
S65VA;S66VA;S41VA;Vm0;Vrest;A3M0Vm0;A3G0A3").
  Proof using . destruct rest as [|x tl]; [left; reflexivity|]. change (last (m0 :: x :: tl) m0) with (last (x :: tl) m0). apply fr_last_in_cons. Qed.
  Lemma fr_flinks_MT q pr nx : ltac2:(tb__ "0|2|
S36S3dS40S3dS0A1M0G0A2M1A1S56VX;Vt;Vq;A3S3cG1S44G0G0Vpr;Vnx;A4A2A3S37S36S3dS1A1S4dVt;Vq;A2S3cS1S6Vpr;Vnx;A2A2A3S36S42S50Vq;VX;A2S45A3A2F_;").
  Proof using .
    unfold flinks, MTX. intros H. destruct (memb q X) eqn:Em; [discriminate|]. destruct (MT t q) as [[p n| |a]|]; try discriminate.
    injection H as -> ->. auto.
  Qed.
  Lemma fr_member ms q : ltac2:(tb__ "0|0|
S5fS56VX;Vt;A2S1aVt;A1Vms;A3S65S0Vq;Vms;A3S39S0S0S39S0S0S37S36S3dS1A1S4dVt;Vq;A2S3cS1S6S3cS0R2A2S3cS0R1A2A2A2A3S37S65S0R2Vms;A3S37S65S0R1Vms;A3S37S65S0Vq;S51Vt;A1A3S36S42S50Vq;VX;A2S45A3A2A2A2A2Lnx;A2Lpr;A2F_;F_;").
  Proof using .
    intros Rg Hin. destruct (ring_links _ _ _ _ Rg Hin) as (pr & nx & HLk).
    pose proof Rg as [[Hnd Hch] Hhd]. destruct ms as [|m0 rest] eqn:Ems; [destruct Hin|]. cbn [cycle_ok] in Hch.
    destruct (chain_next _ _ _ _ _ _ _ Hch Hin HLk) as (l1 & l2 & El & Enx & Epr). injection Enx as ->. injection Epr as ->.
    destruct (fr_flinks_MT q _ _ HLk) as [M Em]. exists (last l1 (last (m0 :: rest) m0)), (hd m0 l2). split; [exact M|].
    split.
    { pose proof (fr_last_in_cons l1 (last (m0 :: rest) m0)) as H1. destruct H1 as [H1|H1].
      - rewrite <- H1. apply fr_last_hd_in.
      - assert (HH : forall y, In y l1 -> In y (m0 :: rest)) by (intros y Hy; rewrite El; apply in_app_iff; left; exact Hy). apply HH. exact H1. }
    split.
    { destruct l2 as [|y tl]; [left; reflexivity|]. rewrite El. apply in_app_iff. right. right. left. reflexivity. }
    split; [eapply MT_Some_In_keys; exact M | exact Em].
  Qed.
  Theorem free_ring_head fm : ltac2:(tb__ "0|2|
S36S3dS0A1S1aVt;A1S3cS0Vfm;A2A3S39S0S0S39S0S0S39S0S0S39S0S0S37S36S3dS1A1M0S4dVt;Vfm;A2S3cS1S6S3cS0R4A2S3cS0R3A2A2A2A3S37S36G0S4dVt;R4A2S3cS1S6S3cS0R2A2S3cS0R1A2A2A2A3S37S36S42S50Vfm;VX;A2S45A3S37S36S42S50R4VX;A2S45A3S37S65S0Vfm;S51Vt;A1M1A3S65S0R4G1A3A2A2A2A2A2Lnx2;A2Lpr2;A2Lnx;A2Lhp;A2F_;").
  Proof using HI.
    intros Hfh. destruct (proj1 (inv_rings HI)) as (ms & Rg & _).
    pose proof (proj1 (ring_head_In _ _ _ ltac:(rewrite Hfh in Rg; exact Rg))) as Hin.
    destruct (fr_member ms fm Rg Hin) as (hp & nx & M1 & Hp & _ & K1 & X1).
    destruct (fr_member ms hp Rg Hp) as (pr2 & nx2 & M2 & _ & _ & K2 & X2).
    exists hp, nx, pr2, nx2. auto 10.
  Qed.
End FreeRing.

Section ForgetUpd.
  Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (t : astate) (gP : sptr) (amP : ameta) (iP : Z) (frP : frame).
  Hypothesis HI : ltac2:(tb__ "0|0|
S4fVX;VR;VU;Vt;A4").
  Hypothesis HuP : ltac2:(tb__ "0|0|
S4eVX;Vt;VgP;VamP;A4").
  Hypothesis HiP : ltac2:(tb__ "0|0|
S37S67Z0ViP;A2S67ViP;S4VamP;A1A2A2").
  Hypothesis HfrP : ltac2:(tb__ "0|0|
S36S3dScA1S16SdVamP;ViP;A2A1S3cScVfrP;A2A3").
  Hypothesis HkP : ltac2:(tb__ "0|0|
S36S1eS1fVfrP;A1S1bA3").
  Definition am_forget : ameta := ltac2:(tb__ "0|0|
S33VamP;ViP;S21S23SdVamP;ViP;A2A1S3eScA1A2A3").
  Let t' : astate := ltac2:(tb__ "0|0|
S75VgP;S5S64A1Vt;A3").

  Lemma fu_MgP : ltac2:(tb__ "0|0|
S36S3dS1A1S4dVt;VgP;A2S3cS1S5VamP;A1A2A3"). Proof using HuP. exact (proj1 (usedX_MT _ _ _ _ HuP)). Qed.
  Lemma fu_ND : NoDup (keys t). Proof using HI. exact (proj1 (inv_keys HI)). Qed.
  Lemma fu_len : ltac2:(tb__ "0|0|
S36S4bS4aS19S29VamP;A1A2S6eS68S4VamP;A1Z1A2A1A3").
  Proof using HI HuP. pose proof (inv_groups HI gP amP HuP) as ((_ & _ & Glen & _) & _). exact Glen. Qed.
  Lemma fu_off : fr_off frP = 0.
  Proof using HI HfrP HiP HkP HuP. exact (proj2 (fgroup_frame X R U t HI gP amP iP frP HuP HiP HfrP HkP)). Qed.
  Lemma fu_nth j : ltac2:(tb__ "0|0|
S67Z0Vj;A2S36S19SdS64Vj;A2S42S19L_;S6aVj;ViP;A2S21S23SdVamP;ViP;A2A1S3eScA1A2SdVamP;Vj;A2X42x2A3F_;").
  Proof using HI HiP HuP. intros Hj. unfold am_forget. apply nth_slot_upd_slot; [lia | exact Hj |]. rewrite fu_len. lia. Qed.
  Lemma fu_fields : ltac2:(tb__ "0|0|
S37S36S0S7S64A1S7VamP;A1A3S37S36S3bS4S64A1S4VamP;A1A3S37S36S3bS2S64A1S2VamP;A1A3S37S36S3bS8S64A1S8VamP;A1A3S37S36S3bS18S64A1S18VamP;A1A3S37S36S3bS55S64A1S55VamP;A1A3S3bS36S0S13S64R1A2S13VamP;R1A2A3Fj;A2A2A2A2A2A2").
  Proof using . exact (upd_slot_fields amP iP _). Qed.

  Lemma fu_slot_cells j : ltac2:(tb__ "0|0|
S67Z0Vj;A2S36S3fS53A1S5aS64Vj;A2S5aVamP;Vj;A2A3F_;").
  Proof using HI HfrP HiP HkP HuP.
    intros Hj. pose proof fu_fields as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
    unfold slot_cells. rewrite (F7 j), (fu_nth j Hj).
    destruct (j =? iP) eqn:E; [|unfold hdr_byte3, hdr_off16, rsv_code, reserved_of; rewrite F5; reflexivity].
    apply Z.eqb_eq in E. subst j. cbn [ss_hdr ss_fr]. rewrite HfrP, fu_off. reflexivity.
  Qed.
  Lemma fu_group_cells : ltac2:(tb__ "0|0|
S36S3fS53A1S57VgP;S64A2S57VgP;VamP;A2A3").
  Proof using HI HfrP HiP HkP HuP.
    pose proof fu_fields as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
    rewrite !group_cells_eq. rewrite F2, F1.
    replace (aidx_cell am_forget) with (aidx_cell amP) by (unfold aidx_cell, am_forget; destruct amP; reflexivity).
    f_equal. f_equal. apply flat_map_ext_In. intros j Hj. apply In_zseq in Hj. apply fu_slot_cells. lia.
  Qed.
  Lemma fu_footer : ltac2:(tb__ "0|0|
S36S3fS53A1S7fS64A1S7fVamP;A1A3").
  Proof using HI HfrP HiP HkP HuP.
    pose proof fu_fields as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
    unfold group_footer_cells, trailing_cell, trailing_loc. rewrite F5, F1, F2. f_equal.
    apply flat_map_ext_In. intros j Hj. apply In_zseq in Hj. rewrite (fu_nth j ltac:(lia)).
    destruct (j =? iP) eqn:E.
    - apply Z.eqb_eq in E. subst j. cbn [ss_fr]. rewrite HfrP. unfold frame_footer_cells. rewrite HkP. reflexivity.
    - destruct (ss_fr (nth_slot amP j)) as [fr|]; [|reflexivity].
      unfold frame_footer_cells, frame_ptr, reserved_of, slot_end. rewrite (F7 j), F5. reflexivity.
  Qed.
  Lemma fu_meta_cells : ltac2:(tb__ "0|0|
S36S3fS53A1S59VgP;S3cS1S5S64A1A2A2S59VgP;S3cS1S5VamP;A1A2A2A3").
  Proof using HfrP HiP HuP. unfold am_forget, meta_slot_cells, meta_bits. destruct amP; reflexivity. Qed.
  Lemma fu_blocks : ltac2:(tb__ "0|1|
S36S3fS40S40S0S3bA2M0G0A2A1S77VgP;S64A2S77VgP;VamP;A2A3").
  Proof using HI HfrP HiP HkP HuP.
    unfold am_forget. apply blocks_of_upd_slot_same; [exact HiP | exact fu_len |].
    unfold slotst_block, slot_block. cbn [ss_fr]. rewrite HfrP, HkP. reflexivity.
  Qed.
  Lemma fu_user_blocks : ltac2:(tb__ "0|0|
S36S3fS40S0S3bA2A1S5bVt';A1S5bVt;A1A3").
  Proof using HI HfrP HiP HkP HuP.
    destruct (upd_used_metas t gP amP am_forget fu_ND fu_MgP) as (l1 & l2 & E1 & E2 & _).
    unfold user_blocks. unfold t' in *. rewrite E1, E2, !flat_map_app. cbn [flat_map]. f_equal. f_equal.
    cbn [snd]. pose proof fu_fields as (F1 & F2 & F3 & F4 & F5 & F6 & F7). rewrite F2.
    apply flat_map_ext_In. intros j Hj. apply In_zseq in Hj. rewrite (F7 j), (fu_nth j ltac:(lia)).
    destruct (j =? iP) eqn:E; [|reflexivity]. apply Z.eqb_eq in E. subst j. cbn [ss_fr]. rewrite HfrP, HkP. reflexivity.
  Qed.
  Lemma fu_footers : ltac2:(tb__ "0|0|
S36S3fS53A1S7eVt';A1S7eVt;A1A3").
  Proof using HI HfrP HiP HkP HuP.
    destruct (upd_used_metas t gP amP am_forget fu_ND fu_MgP) as (l1 & l2 & E1 & E2 & _).
    unfold footer_cells. unfold t' in *. rewrite E1, E2, !flat_map_app. cbn [flat_map snd]. rewrite fu_footer. reflexivity.
  Qed.
  Theorem delta_forget : ltac2:(tb__ "0|0|
S7cVt;Vt';S47S52A1A3").
  Proof using HI HfrP HiP HkP HuP.
    unfold delta. rewrite fu_user_blocks, fu_footers.
    repeat split; try reflexivity.
    - unfold t' in *. apply keys_upd_In. eapply MT_Some_In_keys. exact fu_MgP.
    - intros c Hc. left. apply in_app_iff in Hc as [Hc|Hc]; apply in_app_iff; [left | right; exact Hc].
      destruct (upd_image_In t gP amP am_forget fu_ND fu_MgP c Hc) as [H|[H|H]]; [exact H | |].
      + rewrite fu_meta_cells in H. apply (meta_cells_in_imageI X R U t HI gP c (MT_Some_In_keys _ _ _ fu_MgP)). rewrite fu_MgP. exact H.
      + rewrite fu_group_cells in H. exact (In_image_group t gP amP c (used_metas_g_old t gP amP am_forget fu_ND fu_MgP) H).
  Qed.
  Lemma fu_shape : shape_kept t t'.
  Proof using HuP iP.
    intros q a'. unfold t' in *. rewrite MT_upd. destruct (sptr_eqb q gP) eqn:E; intros M.
    - injection M as <-. exists amP. apply sptr_eqb_eq in E. subst q. pose proof fu_fields as (F1 & F2 & F3 & F4 & _). split; [exact fu_MgP|].
      repeat split; try assumption; try reflexivity.
    - exists a'. auto 7.
  Qed.
End ForgetUpd.

Section FreeGroupNested.
  Local Open Scope mm_scope.
  Variables (X : list sptr) (U : Z -> Z) (s : astate) (g : sptr) (am : ameta) (i : Z).
  Hypothesis HI : ltac2:(tb__ "0|0|
S4fVX;S3cS40S0S3bA2S44S0S3bVg;Vi;A4A2VU;Vs;A4").
  Hypothesis Hu : ltac2:(tb__ "0|0|
S4eVX;Vs;Vg;Vam;A4").
  Hypothesis HU : forall c, 0 <= U c.
  Hypothesis HR2g : ltac2:(tb__ "0|2|
S38S36S40S3dS0A1M0G0A2S44G0G0S11Vam;A1SbVam;A1A4S44G0G0S3eS0A1M1G1A4A3A1S38S36G0S54Vs;S2Vam;A1A2S3cS0Vg;A2A3A1S38S36S3bS10Vam;A1Z0A3A1F_;F_;").
  Hypothesis Hall : ltac2:(tb__ "0|0|
S36S3bS68S73Vam;A1S1dVi;A1A2S22S4Vam;A1A1A3").
  Hypothesis Hsc : ltac2:(tb__ "0|1|
S37S67Z0S2Vam;A1M0A2S69G0Z30A2A2").
  Hypothesis Hml0 : am_maplen am = 0.
  Let sc : Z := am_sc am.

  Hypothesis Hlinks : ltac2:(tb__ "0|2|
S0S36S3dS0A1M0SbVam;A1S3cS0R1A2A3S38S36S0R2Vg;A3A1S39S0S0S39S1S1S39S1S1S37S36G0S11Vam;A1S3cS0R3A2A3S37S38S36S0R3Vg;A3A1S37S36S3dS1A1M1S4dVs;R3A2S3cS1R2A2A3S36G1S4dS75R3S35R2S49G0G0S2dR2A1A3S3cS0R6A2A3Vs;A3R6A2S3cS1R1A2A3A2A2A2Lxn;A2Lxp;A2Lp;A2F_;F_;Fn;").
  Hypothesis HnU : ltac2:(tb__ "0|0|
S0S36S3dS0A1SbVam;A1S3cS0R1A2A3S39S3S3S36S3dS1A1S4dVs;R3A2S3cS1S5R1A1A2A3Lan;A2F_;Fn;").
  Hypothesis Hact : ltac2:(tb__ "0|1|
S0S3S36S3dS0A1M0SbVam;A1S3cS0R2A2A3S38S36S0R3Vg;A3A1S36G0S54Vs;Vsc;A2S3cS0Vg;A2A3S36S3dS1A1S4dS71Vs;Vg;Vam;A3R5A2S3cS1S5R4A1A2A3S36S3bS14R5A1Z0A3F_;F_;F_;F_;Fan;Fn;").
  Hypothesis HactU : ltac2:(tb__ "0|1|
S0S36S3dS0A1M0SbVam;A1S3cS0R1A2A3S38S36S0R2Vg;A3A1S36G0S54Vs;Vsc;A2S3cS0Vg;A2A3S39S3S3S36S3dS1A1S4dS71Vs;Vg;Vam;A3R5A2S3cS1S5R1A1A2A3Lan;A2F_;F_;F_;Fn;").

  Variables (gP : sptr) (amP : ameta) (iP : Z) (frP : frame).
  Hypothesis HuP : ltac2:(tb__ "0|0|
S4eVX;Vs;VgP;VamP;A4").
  Hypothesis HiP : ltac2:(tb__ "0|0|
S37S67Z0ViP;A2S67ViP;S4VamP;A1A2A2").
  Hypothesis HfrP : ltac2:(tb__ "0|0|
S36S3dScA1S16SdVamP;ViP;A2A1S3cScVfrP;A2A3").
  Hypothesis HkP : ltac2:(tb__ "0|0|
S36S1eS1fVfrP;A1S1bA3").
  Hypothesis Hmem : ltac2:(tb__ "0|0|
S36S0S7Vam;A1S13VamP;ViP;A2A3").
  Hypothesis HscP : ltac2:(tb__ "0|0|
S69Vsc;S2VamP;A1A2").

  Definition amP' : ameta := am_forget amP iP.
  Definition fgn_s2 : astate := ltac2:(tb__ "0|0|
S72Vs;Vg;Vam;A3").
  Definition fgn_s3 : astate := ltac2:(tb__ "0|0|
S75VgP;S5S60A1S61A3").
  Definition fgn_s3v : astate := ltac2:(tb__ "0|1|
S75Vg;S6S3eS0A1M0G0A2S63A3").

  Lemma Mg : ltac2:(tb__ "0|0|
S36S3dS1A1S4dVs;Vg;A2S3cS1S5Vam;A1A2A3"). Proof using Hu. exact (proj1 (usedX_MT _ _ _ _ Hu)). Qed.
  Lemma NXg : ltac2:(tb__ "0|0|
S36S42S50Vg;VX;A2S45A3"). Proof using Hu. exact (proj2 (usedX_MT _ _ _ _ Hu)). Qed.
  Lemma Kg : ltac2:(tb__ "0|0|
S65S0Vg;S51Vs;A1A3"). Proof using Hu. exact (MT_Some_In_keys _ _ _ Mg). Qed.
  Lemma MgP : ltac2:(tb__ "0|0|
S36S3dS1A1S4dVs;VgP;A2S3cS1S5VamP;A1A2A3"). Proof using HuP. exact (proj1 (usedX_MT _ _ _ _ HuP)). Qed.
  Lemma NXgP : ltac2:(tb__ "0|0|
S36S42S50VgP;VX;A2S45A3"). Proof using HuP. exact (proj2 (usedX_MT _ _ _ _ HuP)). Qed.
  Lemma HgPg : gP <> g.
  Proof using Hsc HscP Hu HuP. intros E. pose proof (usedX_fun _ _ _ _ _ HuP ltac:(rewrite E; exact Hu)) as E2. unfold sc in HscP. rewrite E2 in HscP. lia. Qed.
  Lemma Hmask : ltac2:(tb__ "0|0|
S36S3bS68S6bS10Vam;A1S14Vam;A1A2S1dVi;A1A2S22S4Vam;A1A1A3").
  Proof using Hall. exact Hall. Qed.
  Lemma Hnofr : ltac2:(tb__ "0|0|
S3bS36S3dScA1S16SdVam;R1A2A1S3eScA1A3Fj;").
  Proof using HI Hall Hu. exact (frameless_of_mask X U s g i am HI Hu Hmask). Qed.

  Let U1 : Z -> Z := ltac2:(tb__ "0|0|
S3bS68VU;R1A1S5eVX;Vs;R1Vg;A4A2Lc;").

  Lemma step1 : ltac2:(tb__ "0|9|
S80S40S43S9A2M0S3dS0A1M1S27S43A1M2Lx;SbVam;A1S0S12S43S43S2eS6cVsc;Z30A2Z5A2S43S12G1S43S2cS26Vsc;A1M3A1M4G1S31R1S3cS0Vg;A2A2S42S12S43S43S2aG3Vg;A2S43S12G1S43G4G1S42G2Lactivate_new;R3G1G2Lhd';R1S0S12S3bS43S28R1A1S3bS32S43S48A2M5L_;A4Lh;G5X3dx2G5X42x2Lhd';A4L_;A4Tactivate_new;Lhd;A4L_;A4Ls0;G5X3dx2Vs;A1G0S4cS43S9R1A3S9S37S4fS41S0Vg;VX;A3M6S3eS40S0S3bA2A1VU1;R1A4S37S36S3dS1A1M7S4dR1Vg;A2S3cS1S5SfS3eS0A1M8G8Vam;A3A1A2A3S37S36S3fS3bA1S17R1A1S17Vs;A1A3S37S36S3fS15A1SeR1A1SeVs;A1A3S37S78VX;Vs;R1A3S37S0S3S4eG6R3R2R1A4S39S3S3S37S4eVX;Vs;R4R1A4S37S36S0S7R3A1S7R1A1A3S37S36S3bS8R3A1S8R1A1A3S37S36S3bS4R3A1S4R1A1A3S37S36S3bS2R3A1S2R1A1A3S36S3bSaR3A1SaR1A1A3A2A2A2A2A2La0;A2F_;Fa;Fq;S37S0S3S4eVX;Vs;R2R1A4S38S36S3bS2R2A1Vsc;A3A1F_;Fa;S38S36S0R2Vg;A3A1S36G7S4dR4R3A2S4dVs;R3A2A3F_;F_;Fq;S76Vs;R1A2A2A2A2A2A2A2A2Ts1;Lr;A3").
  Proof using HI HR2g Hact HactU Hall Hlinks Hmem Hml0 HnU Hsc HscP Hu.
    pose proof Mg as Mg0. pose proof Hnofr as Hnofr0.
    destruct (am_next am) as [nx|] eqn:Enx.
    - mbinds. apply itok_massert; [apply Z.ltb_lt; unfold sc; lia|]. msimp. mbinds. apply itok_get_head. msimp.
      change (nth (Z.to_nat sc) (st_active s) None) with (active_hd s sc). cbn zeta.
      mbinds. eapply (dequeue_exempt_spec X (Some (g, i)) U s sc g am); [exact HI | unfold sc; lia | exact Hu | reflexivity | rewrite Enx; intros E; discriminate | exact Hnofr0 | intros p j E; injection E; auto |].
      intros s1 HI1 Sb1 Mg1 EH1 Mo1 Bwd1 Hk1 Hnew1 UB1. msimp. mbinds. apply itok_get_head. msimp.
      change (nth (Z.to_nat sc) (st_active s1) None) with (active_hd s1 sc).
      pose proof Sb1 as (_&_&_&_&_&_&_&_&_&Eus1&_&_&_&_&Erg1&_&EK1).
      assert (C1 : forall q a, usedX (g :: X) s1 q a -> exists a0, usedX X s q a0 /\ am_mem a = am_mem a0 /\ am_maplen a = am_maplen a0 /\ am_last a = am_last a0 /\ am_sc a = am_sc a0 /\ am_aidx a = am_aidx a0).
      { intros q a Hq. destruct (Bwd1 q a Hq) as (_ & a0 & H0 & E). pose proof (strip_fields _ _ E) as (Em&_&_&El&Es&Eml&Eai&_).
        exists a0. auto 7. }
      assert (Cr1 : corr X s s1).
      { intros q a Hq. destruct (sptr_eq_dec q g) as [->|Hne].
        - pose proof (usedX_MT _ _ _ _ Hq) as [M _]. rewrite Mg1 in M. injection M as <-. exists am.
          split; [exact Hu|]. destruct am; repeat split; reflexivity.
        - destruct (C1 q a ltac:(apply usedX_cons; assumption)) as (a0 & H0 & E0 & F0 & _). exists a0. auto. }
      assert (POST1 : forall s1', Inv (g :: X) None U1 s1' ->
                (exists h x, s1' = upd_meta h x s1 /\ h <> g /\
                   (exists ah ah', x = MUsed ah' /\ usedX (g :: X) s1 h ah /\ am_sc ah = sc /\ am_mem ah' = am_mem ah /\ am_maplen ah' = am_maplen ah /\
                      am_last ah' = am_last ah /\ am_sc ah' = am_sc ah /\ am_aidx ah' = am_aidx ah /\ blocks_of h ah' = blocks_of h ah)) \/ s1' = s1 ->
                let s1 := s1' in
                Inv (g :: X) None U1 s1 /\ MT s1 g = Some (MUsed (am_set_links None None am)) /\
                st_usage s1 = st_usage s /\ st_regions s1 = st_regions s /\ corr X s s1 /\
                (forall q a, usedX (g :: X) s1 q a -> exists a0, usedX X s q a0 /\ am_mem a = am_mem a0 /\ am_maplen a = am_maplen a0 /\ am_last a = am_last a0 /\ am_sc a = am_sc a0 /\ am_aidx a = am_aidx a0) /\
                (forall q, (forall a, usedX X s q a -> am_sc a <> sc) -> q <> g -> MT s1 q = MT s q) /\ ub_same s s1).
      { intros s1' HI1' Hcase. cbn zeta. destruct Hcase as [(h & x & -> & Hhg & ah & ah' & -> & Uh & Sh & Emh & Emlh & Elh & Esh & Eah & Ebl) | ->].
        - split; [exact HI1'|]. split; [rewrite MT_upd_other by (intros E; exact (Hhg (eq_sym E))); exact Mg1|].
          split; [exact Eus1|]. split; [exact Erg1|].
          assert (C2 : forall q a, usedX (g :: X) (upd_meta h (MUsed ah') s1) q a ->
                       exists a0, usedX X s q a0 /\ am_mem a = am_mem a0 /\ am_maplen a = am_maplen a0 /\ am_last a = am_last a0 /\ am_sc a = am_sc a0 /\ am_aidx a = am_aidx a0).
          { intros q a Hq. apply usedX_upd in Hq. destruct Hq as [(-> & _ & E) | (Hne & Hq)].
            - injection E as <-. destruct (C1 h ah Uh) as (a0 & H0 & E0 & F0 & L0 & S0 & A0). exists a0. split; [exact H0|]. repeat split; congruence.
            - apply C1. exact Hq. }
          split.
          { intros q a Hq. destruct (sptr_eq_dec q g) as [->|Hne].
            - pose proof (usedX_MT _ _ _ _ Hq) as [M _]. rewrite MT_upd_other in M by (intros E; exact (Hhg (eq_sym E))).
              rewrite Mg1 in M. injection M as <-. exists am. split; [exact Hu|]. destruct am; repeat split; reflexivity.
            - destruct (C2 q a ltac:(apply usedX_cons; assumption)) as (a0 & H0 & E0 & F0 & _). exists a0. auto. }
          split; [exact C2|]. split.
          { intros q Hq Hqg. destruct (sptr_eq_dec q h) as [->|Hqh].
            + exfalso. destruct (Bwd1 h ah Uh) as (_ & a0 & H0 & E0). pose proof (strip_fields _ _ E0) as (_&_&_&_&Es&_).
              apply (Hq a0 H0). congruence.
            + rewrite MT_upd_other by exact Hqh. apply Mo1; assumption. }
          eapply ub_same_trans; [exact UB1|]. apply ub_same_upd_In; [eapply MT_Some_In_keys; exact (proj1 (usedX_MT _ _ _ _ Uh))|].
          rewrite (proj1 (usedX_MT _ _ _ _ Uh)). cbn. exact Ebl.
        - split; [exact HI1'|]. split; [exact Mg1|]. split; [exact Eus1|]. split; [exact Erg1|]. split; [exact Cr1|]. split; [exact C1|]. split; [exact Mo1 | exact UB1]. }
      destruct (osptr_eqb (active_hd s sc) (Some g)) eqn:Ehd.
      + apply osptr_eqb_eq in Ehd. destruct (Hnew1 Ehd) as [Hnone | (h & ah & Hh & Hhg & Uh & Sh & Avh)].
        * rewrite Hnone. apply itok_ret. cbn [snd]. apply (POST1 s1 HI1). right. reflexivity.
        * rewrite Hh. mbinds. eapply activate_group_spec; [exact HI1 | exact Hsc | exact Uh | exact Sh | exact Hh | exact Avh |].
          intros mk s2 HI2 Es2. msimp. apply itok_ret. cbn [snd]. apply (POST1 s2 HI2). left.
          eexists h, _. split; [exact Es2|]. split; [exact Hhg|]. eexists ah, _. split; [reflexivity|]. split; [exact Uh|]. split; [exact Sh|].
          split; [destruct ah; reflexivity|]. split; [destruct ah; reflexivity|]. split; [destruct ah; reflexivity|]. split; [destruct ah; reflexivity|]. split; [destruct ah; reflexivity|].
          apply blocks_of_ext; destruct ah; reflexivity.
      + apply itok_ret. cbn [snd]. apply (POST1 s1 HI1). right. reflexivity.
    - apply itok_ret. cbn [snd].
      assert (Hp : am_prev am = None) by (eapply unlinked_of_next_None; eauto).
      split; [apply (Inv_exempt X (Some (g, i)) U s g am HI Hu Hnofr0 Hp Enx); intros p j E; injection E; auto|].
      split; [rewrite Mg0; destruct am; cbn in Hp, Enx |- *; subst; reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply corr_refl|]. split.
      + intros q a Hq. apply usedX_cons_inv in Hq as [_ Hq]. exists a. auto 7.
      + split; [intros; reflexivity | apply ub_same_refl].
  Qed.

  Lemma s1_facts_model : ltac2:(tb__ "0|3|
S70Vs;Vg;Vam;A3S9S37S4fS41S0Vg;VX;A3M0S3eS40S0S3bA2A1VU1;R1A4S37S36S3dS1A1M1S4dR1Vg;A2S3cS1S5SfS3eS0A1M2G2Vam;A3A1A2A3S37S36S3fS3bA1S17R1A1S17Vs;A1A3S37S36S3fS15A1SeR1A1SeVs;A1A3S37S78VX;Vs;R1A3S37S0S3S4eG0R3R2R1A4S39S3S3S37S4eVX;Vs;R4R1A4S37S36S0S7R3A1S7R1A1A3S37S36S3bS8R3A1S8R1A1A3S37S36S3bS4R3A1S4R1A1A3S37S36S3bS2R3A1S2R1A1A3S36S3bSaR3A1SaR1A1A3A2A2A2A2A2La0;A2F_;Fa;Fq;S37S0S3S4eVX;Vs;R2R1A4S38S36S3bS2R2A1Vsc;A3A1F_;Fa;S38S36S0R2Vg;A3A1S36G1S4dR4R3A2S4dVs;R3A2A3F_;F_;Fq;S76Vs;R1A2A2A2A2A2A2A2A2Ts1;").
  Proof using HI HR2g Hact HactU Hall Hlinks Hmem Hml0 HnU Hsc HscP Hu.
    exact (itok_of_eq _ _ _ step1 (fgm_dq_eq X U s g am i HI Hu HR2g Hsc Hlinks HnU Hact HactU)).
  Qed.

  Lemma HU1 c : ltac2:(tb__ "0|1|
S37S67Z0M0Vc;A2S69Vc;Z30A2A2S36S3bVU1;Vc;A1S68VU;Vc;A1S42S3bL_;S6aVsc;Vc;A2S68S4Vam;A1Z1A2G0X42x2A2A3F_;").
  Proof using Hu. intros Hc. unfold U1. rewrite (contrib_used X s c g am Hu). reflexivity. Qed.

  Lemma usage_ge : ltac2:(tb__ "0|0|
S67S68S4Vam;A1Z1A2S34Vs;Vsc;A2A2").
  Proof using HI HU Hsc Hu U1 iP.
    rewrite (inv_usage HI sc ltac:(unfold sc; lia)). pose proof (class_sum_ge_contrib X _ U s sc g HI Kg) as Hge.
    rewrite (contrib_used X s sc g am Hu) in Hge. unfold sc in Hge |- *. rewrite Z.eqb_refl in Hge. pose proof (HU (am_sc am)). lia.
  Qed.

  Lemma s2_facts_model : ltac2:(tb__ "0|1|
S37S4fS41S0Vg;VX;A3S3eS40S0S3bA2A1VU;S61A4S37S36S3fS40S0S1A2A1S25S61A1S25S70Vs;Vg;Vam;A3M0A1A3S37S36S3fS15A1SeS61A1SeVs;A1A3S37S36S3fS3dS0A1A1S24S61A1S24G0A1A3S37S76Vs;S61A2S0S36S3dS1A1S4dS61R1A2S4dG0R1A2A3Fq;A2A2A2A2A2").
  Proof using HI HR2g HU Hact HactU Hall Hlinks Hmem Hml0 HnU Hsc HscP Hu.
    destruct s1_facts_model as (HI1 & Mg1 & Eus1 & Erg1 & Cr1 & C1 & Mo1 & UB1).
    pose proof usage_ge as Hv.
    pose proof (Inv_set_usage (g :: X) None U1 (fgm_s1 s g am) sc (usage_of s sc - (am_last am + 1)) HI1 ltac:(unfold sc; lia) ltac:(lia)) as HI2.
    assert (MT2 : forall q, MT fgn_s2 q = MT (fgm_s1 s g am) q) by (intros q; reflexivity).
    split; [|split; [reflexivity | split; [exact Erg1 | split; [reflexivity | split; [|exact MT2]]]]].
    - unfold fgn_s2, fgm_s2. fold sc.
      eapply Inv_U_ext; [|exact HI2]. intros c Hc. unfold Uadd. rewrite (HU1 c Hc).
      replace (usage_of (fgm_s1 s g am) sc) with (usage_of s sc) by (unfold usage_of; rewrite Eus1; reflexivity).
      destruct (c =? sc) eqn:E1; destruct (sc =? c) eqn:E2; try lia;
        try (apply Z.eqb_eq in E1; apply Z.eqb_neq in E2; lia); try (apply Z.eqb_neq in E1; apply Z.eqb_eq in E2; lia).
    - eapply ub_same_trans; [exact UB1|]. apply ub_same_metas. reflexivity.
  Qed.

  Lemma MT2 q : ltac2:(tb__ "0|0|
S36S3dS1A1S4dS61Vq;A2S4dS70Vs;Vg;Vam;A3Vq;A2A3"). Proof using . reflexivity. Qed.
  Lemma EU2 Y q a : ltac2:(tb__ "0|0|
S3aS4eVY;S61Vq;Va;A4S4eVY;S70Vs;Vg;Vam;A3Vq;Va;A4A2").
  Proof using HiP Hsc U1 i. unfold usedX, MTX. rewrite MT2. tauto. Qed.

  Lemma MgP2 : ltac2:(tb__ "0|0|
S36S3dS1A1S4dS61VgP;A2S3cS1S5VamP;A1A2A3").
  Proof using HI HR2g Hact HactU Hall Hlinks Hmem Hml0 HnU Hsc HscP Hu HuP U1.
    destruct s1_facts_model as (_ & _ & _ & _ & _ & _ & Mo1 & _). rewrite MT2, (Mo1 gP); [exact MgP | | exact HgPg].
    intros a Ha. pose proof (usedX_fun _ _ _ _ _ Ha HuP) as ->. unfold sc in HscP |- *. lia.
  Qed.
  Lemma HuP2 : ltac2:(tb__ "0|0|
S4eS41S0Vg;VX;A3S61VgP;VamP;A4").
  Proof using HI HR2g Hact HactU Hall Hlinks Hmem Hml0 HnU Hsc HscP Hu HuP U1.
    apply usedX_intro; [|exact MgP2]. rewrite memb_cons, NXgP.
    replace (sptr_eqb gP g) with false by (symmetry; apply sptr_eqb_neq; exact HgPg). reflexivity.
  Qed.
  Lemma C2 q a : ltac2:(tb__ "0|0|
S4eS41S0Vg;VX;A3S61Vq;Va;A4S39S3S3S37S4eVX;Vs;Vq;R1A4S37S36S0S7Va;A1S7R1A1A3S37S36S3bS8Va;A1S8R1A1A3S37S36S3bS4Va;A1S4R1A1A3S37S36S3bS2Va;A1S2R1A1A3S36S3bSaVa;A1SaR1A1A3A2A2A2A2A2La0;A2F_;").
  Proof using HI HR2g Hact HactU Hall HiP Hlinks Hmem Hml0 HnU Hsc HscP Hu U1. intros Hq. destruct s1_facts_model as (_ & _ & _ & _ & _ & C1 & _). apply C1. apply EU2. exact Hq. Qed.

  Lemma s3_facts_model : ltac2:(tb__ "0|1|
S37S4fS41S0Vg;VX;A3M0S3cS40S0S3bA2S44S0S3bVgP;ViP;A4A2VU;S63A4S4eG0S63VgP;S60A4A2").
  Proof using HI HR2g HU Hact HactU Hall HfrP HiP Hlinks Hmem Hml0 HnU Hsc HscP Hu HuP.
    destruct s2_facts_model as (HI2 & _).
    pose proof (forget_frame_spec (g :: X) U fgn_s2 gP iP amP frP (fun r => Inv (g :: X) (Some (gP, iP)) U (snd r) /\ snd r = fgn_s3) HI2 HuP2 HiP HfrP) as T.
    assert (NS : forall c ac, usedX (g :: X) fgn_s2 c ac -> am_maplen ac = 0 -> am_mem ac <> slot_start amP iP).
    { intros c ac Hc Hmlc Emc. pose proof (usedX_cons_inv _ _ _ _ _ Hc) as [Hcg _].
      destruct (C2 c ac Hc) as (ac0 & H0 & E0 & _).
      eapply (same_mem_contra X _ U s c ac0 g am HI H0 Hu Hcg). rewrite <- E0, Emc. symmetry. exact Hmem. }
    specialize (T NS ltac:(intros s' -> HI3; split; [exact HI3 | reflexivity])).
    assert (EQ : forget_frame gP iP fgn_s2 = IRet (tt, fgn_s3)).
    { unfold forget_frame. rewrite (bind_eq _ _ fgn_s2 amP fgn_s2 (getm_eq fgn_s2 gP amP MgP2)). exact (setm_eq fgn_s2 gP amP'). }
    destruct (itok_of_eq _ _ _ T EQ) as [HI3 _]. cbn [snd] in HI3.
    split; [exact HI3|].
    unfold fgn_s3. apply usedX_upd. left. split; [reflexivity|]. split; [|reflexivity].
    rewrite memb_cons, NXgP. replace (sptr_eqb gP g) with false by (symmetry; apply sptr_eqb_neq; exact HgPg). reflexivity.
  Qed.

  Lemma amP'_fields : ltac2:(tb__ "0|1|
S37S36S0S7S60A1S7VamP;A1A3S37S36S3bS4S60A1S4VamP;A1A3S37S36S3bS2S60A1S2VamP;A1A3S37S36S3bS8S60A1S8VamP;A1A3S37S36S3bS18S60A1S18VamP;A1A3S37S36S3bS55S60A1S55VamP;A1A3S37S3bS36S0S13S60R1A2S13VamP;R1A2A3Fj;S37S36S3dS0A1M0S11S60A1S11VamP;A1A3S37S36G0SbS60A1SbVamP;A1A3S37S36S3bS14S60A1S14VamP;A1A3S37S36S3bS10S60A1S10VamP;A1A3S37S36S3bSaS60A1SaVamP;A1A3S36S3bS58S60A1S58VamP;A1A3A2A2A2A2A2A2A2A2A2A2A2A2").
  Proof using HfrP HiP Hmem HscP HuP. unfold amP', upd_slot, stride_of, group_extent, slot_start, stride_of, meta_bits. destruct amP; cbn. repeat split; reflexivity. Qed.

  Theorem fgn_call : ltac2:(tb__ "0|4|
S37S4fS41S0Vg;VX;A3M0S3cS40S0S3bA2S44S0S3bVgP;ViP;A4A2VU;S62A4S37S4eG0S62VgP;S60A4S37S36S3dS1A1M1S4dS62Vg;A2S3cS1S6S3eS0A1M2G2A2A2A3S37S0S38S36S0R1Vg;A3A1S38S36S0R2VgP;A3A1S36G1S4dS62R3A2S4dS61R3A2A3F_;F_;Fq;S38S36S40S3dS0A1M3G3A2S44G3G3S11S60A1SbS60A1A4S44G3G3G2G2A4A3A1S38S36G3S54S62S2S60A1A2S3cS0VgP;A2A3A1S38S36S3bS10S60A1Z0A3A1F_;F_;A2A2A2A2").
  Proof using HI HR2g HU Hact HactU Hall HfrP HiP HkP Hlinks Hmem Hml0 HnU Hsc HscP Hu HuP.
    destruct s3_facts_model as [HI3 HuP3]. destruct s2_facts_model as (HI2 & _).
    split; [apply (Inv_upd_exempt (g :: X) (Some (gP, iP)) U fgn_s3 g (MFree None None) HI3); [left; reflexivity | exact I]|].
    split; [unfold fgn_s3v; apply usedX_upd; right; split; [exact HgPg | exact HuP3]|].
    split; [apply MT_upd_same|].
    split; [intros q Hqg HqP; unfold fgn_s3v, fgn_s3; rewrite (MT_upd_other g) by exact Hqg; rewrite (MT_upd_other gP) by exact HqP; reflexivity|].

    pose proof amP'_fields as (_ & _ & Fsc & _ & _ & _ & _ & Fp & Fn & _ & Ff & _).
    intros Hl Hnh. rewrite Ff. rewrite Fp, Fn in Hl. rewrite Fsc in Hnh.
    replace (active_hd fgn_s3v (am_sc amP)) with (active_hd fgn_s2 (am_sc amP)) in Hnh by reflexivity.
    pose proof (inv_groups HI gP amP HuP) as (_ & _ & _ & GclP & _).
    assert (HscP48 : 0 <= am_sc amP < 48).
    { destruct GclP as [(C & _) | (C & _)]; [|exact C]. exfalso.
      pose proof (inv_groups HI g am Hu) as (_ & _ & _ & _ & _ & Gns). destruct (Gns Hml0) as (_ & g' & am' & i' & fr' & U' & Hi' & F' & K' & Emem & Hsc' & N63' & _).

      assert (Eptr : am_mem am = frame_ptr am' i' fr').
      { pose proof (inv_groups HI g' am' U') as (_ & _ & Gsl' & _). pose proof (Gsl' i' Hi') as (_ & _ & S3'). rewrite F' in S3'.
        destruct S3' as (_ & _ & (_ & _ & _ & _ & FG') & _). destruct (FG' K') as [Hoff' _].
        unfold frame_ptr. rewrite Hoff', Z.mul_0_r, padd_0. exact Emem. }
      assert (EptrP : am_mem am = frame_ptr amP iP frP).
      { pose proof (inv_groups HI gP amP HuP) as (_ & _ & Gsl & _). pose proof (Gsl iP HiP) as (_ & _ & S3). rewrite HfrP in S3.
        destruct S3 as (_ & _ & (_ & _ & _ & _ & FG) & _). destruct (FG HkP) as [Hoff _].
        unfold frame_ptr. rewrite Hoff, Z.mul_0_r, padd_0. exact Hmem. }
      pose proof (find_frame_in_spec X (Some (g, i)) U s HI g' am' i' fr' U' Hi' F') as FF'. rewrite <- Eptr in FF'.
      pose proof (find_frame_in_spec X (Some (g, i)) U s HI gP amP iP frP HuP HiP HfrP) as FF. rewrite <- EptrP in FF.
      rewrite FF in FF'. injection FF' as EgP _. subst g'. pose proof (usedX_fun _ _ _ _ _ U' HuP) as ->. exact (N63' C). }
    apply (proj2 (proj2 (ring_facts _ _ _ _ _ _ HI2 HuP2 ltac:(lia) ltac:(lia)))); [exact Hl | exact Hnh | intros; discriminate].
  Qed.

  Lemma MT_s3v_other q : ltac2:(tb__ "0|0|
S38S36S0Vq;Vg;A3A1S38S36S0Vq;VgP;A3A1S3S4eVX;Vs;Vq;R1A4S38S36S3bS2R2A1Vsc;A3A1F_;Fa;S36S3dS1A1S4dS62Vq;A2S4dVs;Vq;A2A3F_;F_;F_;").
  Proof using HI HR2g HU Hact HactU Hall HfrP HiP HkP Hlinks Hmem Hml0 HnU Hsc HscP Hu HuP U1.
    intros Hqg HqP Hq. destruct fgn_call as (_ & _ & _ & E & _). rewrite (E q Hqg HqP), MT2.
    destruct s1_facts_model as (_ & _ & _ & _ & _ & _ & Mo1 & _). exact (Mo1 q Hq Hqg).
  Qed.
  Lemma xzomb_s3v : ltac2:(tb__ "0|3|
S0S65S0R1VX;A3S36S3dS1A1M0S4dVs;R2A2S3cS1S6S3eS0A1M1G1A2A2M2A3F_;Fx;S0S65S0R1S41S0Vg;VX;A3A3S36G0S4dS62R2A2G2A3F_;Fx;F_;").
  Proof using HI HR2g HU Hact HactU Hall HfrP HiP HkP Hlinks Hmem Hml0 HnU Hsc HscP Hu HuP U1.
    intros HXz x [<- | Hx]; [exact (proj1 (proj2 (proj2 fgn_call)))|].
    pose proof (HXz x Hx) as Mx.
    assert (Hxg : x <> g) by (intros ->; rewrite Mg in Mx; discriminate).
    assert (HxP : x <> gP) by (intros ->; rewrite MgP in Mx; discriminate).
    rewrite (MT_s3v_other x Hxg HxP); [exact Mx|]. intros a Ha. rewrite (proj1 (usedX_MT _ _ _ _ Ha)) in Mx. discriminate.
  Qed.
  Lemma corr_s3v q a : ltac2:(tb__ "0|0|
S4eS41S0Vg;VX;A3S62Vq;Va;A4S39S3S3S37S4eVX;Vs;Vq;R1A4S37S36S0S7Va;A1S7R1A1A3S37S36S3bS8Va;A1S8R1A1A3S37S36S3bS4Va;A1S4R1A1A3S37S36S3bS2Va;A1S2R1A1A3S36S3bSaVa;A1SaR1A1A3A2A2A2A2A2La0;A2F_;").
  Proof using HI HR2g Hact HactU Hall HfrP HiP Hlinks Hmem Hml0 HnU Hsc HscP Hu HuP U1.
    intros Hq. pose proof (usedX_cons_inv _ _ _ _ _ Hq) as [Hqg HqX].
    unfold fgn_s3v, fgn_s3 in Hq. apply usedX_upd in Hq. destruct Hq as [(-> & _ & E) | (_ & Hq)]; [discriminate|].
    apply usedX_upd in Hq. destruct Hq as [(-> & _ & E) | (HqP & Hq)].
    - injection E as <-. exists amP. pose proof amP'_fields as (F1 & F2 & F3 & F4 & _). split; [exact HuP|]. repeat split; try assumption; try reflexivity.
    - exact (C2 q a Hq).
  Qed.

  Lemma ND0 : NoDup (keys s). Proof using HI. exact (proj1 (inv_keys HI)). Qed.
  Lemma KgP2 : In gP (keys fgn_s2). Proof using HI HR2g Hact HactU Hall Hlinks Hmem Hml0 HnU Hsc HscP Hu HuP U1. eapply MT_Some_In_keys. exact MgP2. Qed.
  Lemma am_unlinked : ltac2:(tb__ "0|1|
S36S3dS0A1SbVam;A1S3eS0A1M0A3S36S3SfG0G0Vam;A3Vam;A3F_;").
  Proof using HI HR2g Hact HactU Hall Hlinks Hmem Hml0 HnU Hsc HscP Hu.
    intros En. pose proof (unlinked_of_next_None X (Some (g, i)) U s g am HI Hu Hsc En) as Hp.
    destruct am; cbn in Hp, En |- *; subst; reflexivity.
  Qed.
  Lemma Mg2 : ltac2:(tb__ "0|1|
S36S3dS1A1S4dS61Vg;A2S3cS1S5SfS3eS0A1M0G0Vam;A3A1A2A3").
  Proof using HI HR2g Hact HactU Hall Hlinks Hmem Hml0 HnU Hsc HscP Hu U1. rewrite MT2. destruct s1_facts_model as (_ & M & _). exact M. Qed.
  Lemma Mg3 : ltac2:(tb__ "0|1|
S36S3dS1A1S4dS63Vg;A2S3cS1S5SfS3eS0A1M0G0Vam;A3A1A2A3").
  Proof using HI HR2g Hact HactU Hall Hlinks Hmem Hml0 HnU Hsc HscP Hu HuP U1. unfold fgn_s3. rewrite MT_upd_other; [exact Mg2|]. intros E. exact (HgPg (eq_sym E)). Qed.
  Lemma Kg2 : In g (keys fgn_s2). Proof using HI HR2g Hact HactU Hall Hlinks Hmem Hml0 HnU Hsc HscP Hu U1. eapply MT_Some_In_keys. exact Mg2. Qed.
  Lemma keys_s3 : ltac2:(tb__ "0|0|
S36S3fS0A1S51S63A1S51S61A1A3"). Proof using HI HR2g Hact HactU Hall Hlinks Hmem Hml0 HnU Hsc HscP Hu HuP U1. unfold fgn_s3. apply keys_upd_In. exact KgP2. Qed.
  Lemma keys_s3v : ltac2:(tb__ "0|0|
S36S3fS0A1S51S62A1S51S61A1A3").
  Proof using HI HR2g Hact HactU Hall Hlinks Hmem Hml0 HnU Hsc HscP Hu HuP U1. unfold fgn_s3v. rewrite (keys_upd_In g _ fgn_s3); [exact keys_s3|]. rewrite keys_s3. exact Kg2. Qed.
  Lemma Hnofr' j : ltac2:(tb__ "0|1|
S36S3dScA1S16SdSfS3eS0A1M0G0Vam;A3Vj;A2A1S3eScA1A3").
  Proof using HI Hall Hu. unfold nth_slot, am_set_links. cbn [am_slots]. exact (Hnofr j). Qed.

  Lemma ub_s3v : ub_same s fgn_s3v.
  Proof using HI HR2g HU Hact HactU Hall HfrP HiP HkP Hlinks Hmem Hml0 HnU Hsc HscP Hu HuP U1.
    destruct s2_facts_model as (HI2 & _ & _ & _ & UB2 & _).
    eapply ub_same_trans; [exact UB2|]. eapply ub_same_trans.
    - unfold fgn_s3. apply (ub_same_upd_In fgn_s2 gP (MUsed amP') KgP2). rewrite MgP2. cbn [ucontrib].
      exact (fu_blocks (g :: X) None U fgn_s2 gP amP iP frP HI2 HuP2 HiP HfrP HkP).
    - unfold fgn_s3v. apply ub_same_upd_In; [rewrite keys_s3; exact Kg2|].
      rewrite Mg3. cbn [ucontrib]. symmetry. apply blocks_of_frameless. exact Hnofr'.
  Qed.

  Section Zomb.
  Hypothesis HXz : ltac2:(tb__ "0|1|
S0S65S0R1VX;A3S36S3dS1A1S4dVs;R2A2S3cS1S6S3eS0A1M0G0A2A2A3F_;Fx;").
  Lemma used_s3v q a' : ltac2:(tb__ "0|0|
S36S3dS1A1S4dS62Vq;A2S3cS1S5Va';A1A2A3S4eS41S0Vg;VX;A3S62Vq;Va';A4F_;").
  Proof using HI HR2g HU HXz Hact HactU Hall HfrP HiP HkP Hlinks Hmem Hml0 HnU Hsc HscP Hu HuP U1.
    intros M'. destruct (sptr_eq_dec q g) as [->|Hqg]; [rewrite (proj1 (proj2 (proj2 fgn_call))) in M'; discriminate|].
    apply usedX_intro; [|exact M']. rewrite memb_cons. replace (sptr_eqb q g) with false by (symmetry; apply sptr_eqb_neq; exact Hqg). cbn [orb].
    destruct (memb q X) eqn:Em; [|reflexivity]. exfalso.
    rewrite (xzomb_s3v HXz q ltac:(right; apply memb_In; exact Em)) in M'. discriminate.
  Qed.
  Lemma shape_s3v : shape_kept s fgn_s3v.
  Proof using HI HR2g HU HXz Hact HactU Hall HfrP HiP HkP Hlinks Hmem Hml0 HnU Hsc HscP Hu HuP U1.
    intros q a' M'. destruct (corr_s3v q a' (used_s3v q a' M')) as (a0 & H0 & E1 & E2 & E3 & E4 & E5).
    exists a0. split; [exact (proj1 (usedX_MT _ _ _ _ H0)) | auto 6].
  Qed.
  Lemma hosts_s3v : ltac2:(tb__ "0|0|
S79Vs;A1S79S62A1F_;").
  Proof using HI HR2g HU HXz Hact HactU Hall HfrP HiP HkP Hlinks Hmem Hml0 HnU Hsc HscP Hu HuP U1. exact (hosts_ok_kept s fgn_s3v shape_s3v). Qed.
  Lemma reach_s3v : ltac2:(tb__ "0|0|
S7aVs;A1S7aS62A1F_;").
  Proof using HI HR2g HU HXz Hact HactU Hall HfrP HiP HkP Hlinks Hmem Hml0 HnU Hsc HscP Hu HuP U1. exact (reach_ok_kept s fgn_s3v shape_s3v). Qed.
  End Zomb.

  Lemma tier_par : ltac2:(tb__ "0|0|
S79Vs;A1S81S7bS2VamP;A1A1S7bVsc;A1A2F_;").
  Proof using HiP Hmem Hml0 HscP Hu HuP.
    intros Hh. apply tier_host_lt; [|exact HscP].
    exact (Hh g am gP amP iP Mg Hml0 MgP HiP Hmem).
  Qed.

  Section Delta.
    Variable l1 : list loc.
    Hypothesis D1 : ltac2:(tb__ "0|0|
S7cVs;S70Vs;Vg;Vam;A3Vl1;A3").
    Theorem deltaU_s3v : ltac2:(tb__ "0|1|
S82Vs;S62S46S52S46S52S46S52Vl1;S41S52S5dS68S5cS6dZ8Vsc;A2A2A1S47S52A1M0A3A3G0A3S7dVg;A1A3A3").
    Proof using D1 HI HR2g HU Hact HactU Hall HfrP HiP HkP Hlinks Hmem Hml0 HnU Hsc HscP Hu HuP U1.
      destruct s2_facts_model as (HI2 & _). destruct s3_facts_model as [HI3 HuP3].
      eapply deltaU_trans; [eapply deltaU_trans; [eapply deltaU_trans; [apply delta_U; exact D1|]|]|].
      - unfold fgn_s2, fgm_s2. apply deltaU_usage. unfold sc. lia.
      - apply delta_U. exact (delta_forget (g :: X) None U fgn_s2 gP amP iP frP HI2 HuP2 HiP HfrP HkP).
      - apply delta_U. unfold fgn_s3v.
        apply (delta_nu fgn_s3 g (MUsed (am_set_links None None am)) (MFree None None)).
        + rewrite keys_s3. pose proof D1 as (_&_&_&_&_&_&K1&_). unfold fgn_s2, fgm_s2. cbn [keys set_usage st_metas]. unfold keys in K1 |- *. cbn. rewrite K1. exact ND0.
        + exact Mg3.
        + exact I.
        + intros a E j. injection E as <-. exact (Hnofr' j).
    Qed.
  End Delta.

  Section Finish.
    Variable t4 : astate.
    Hypothesis HI4 : ltac2:(tb__ "0|0|
S4fS41S0Vg;VX;A3S3eS40S0S3bA2A1VU;Vt4;A4").
    Hypothesis HXz4 : ltac2:(tb__ "0|1|
S0S65S0R1S41S0Vg;VX;A3A3S36S3dS1A1S4dVt4;R2A2S3cS1S6S3eS0A1M0G0A2A2A3F_;Fx;").
    Hypothesis Cr4 : ltac2:(tb__ "0|0|
S78S41S0Vg;VX;A3S62Vt4;A3").
    Hypothesis UB4 : ub_same fgn_s3v t4.

    Definition fgn_s5 : astate := fq_post t4 g.

    Lemma Mg4 : ltac2:(tb__ "0|1|
S36S3dS1A1S4dVt4;Vg;A2S3cS1S6S3eS0A1M0G0A2A2A3"). Proof using HXz4. apply HXz4. left. reflexivity. Qed.
    Lemma ND4 : NoDup (keys t4). Proof using HI4. exact (proj1 (inv_keys HI4)). Qed.

    Lemma free_ring4 fm : ltac2:(tb__ "0|1|
S36S3dS0A1S1aVt4;A1S3cS0Vfm;A2A3S39S0S0S39S0S0S39S0S0S39S0S0S37S36S3dS1A1M0S4dVt4;Vfm;A2S3cS1S6S3cS0R4A2S3cS0R3A2A2A2A3S37S36G0S4dVt4;R4A2S3cS1S6S3cS0R2A2S3cS0R1A2A2A2A3S37S38S36S0Vfm;Vg;A3A1S37S38S36S0R4Vg;A3A1S37S36S42S50Vfm;VX;A2S45A3S36S42S50R4VX;A2S45A3A2A2A2A2A2Lnx2;A2Lpr2;A2Lnx;A2Lhp;A2F_;").
    Proof using HI4.
      intros Hfh. destruct (free_ring_head (g :: X) None U t4 HI4 fm Hfh) as (hp & nx & pr2 & nx2 & M1 & M2 & X1 & X2 & _).
      rewrite memb_cons in X1, X2. apply Bool.orb_false_iff in X1 as [X1a X1b]. apply Bool.orb_false_iff in X2 as [X2a X2b].
      apply sptr_eqb_neq in X1a. apply sptr_eqb_neq in X2a.
      exists hp, nx, pr2, nx2. auto 10.
    Qed.

    Lemma free_meta_eq : ltac2:(tb__ "0|1|
S36S20S9S40S43S9A2M0A2S2bVg;Vt4;A2S1cS9G0S44S43S9S48S6fA4A3A3").
    Proof using HI4 HXz4.
      unfold free_meta. Local Open Scope mm_scope.
      rewrite (bind_eq _ _ t4 tt t4).
      - apply queue_free_eq; [exact Mg4|].
        intros fm Hfh. destruct (free_ring4 fm Hfh) as (hp & nx & pr2 & nx2 & M1 & M2 & N1 & N2 & _).
        split; [exact N1|]. exists (MFree (Some hp) (Some nx)), hp. split; [exact M1|]. split; [reflexivity|]. split; [exact N2|]. rewrite M2. discriminate.
      - rewrite setslot_eq. rewrite (upd_meta_same g _ t4 Mg4). reflexivity.
    Qed.

    Theorem fgn_finish : ltac2:(tb__ "0|1|
S37S4fVX;S3eS40S0S3bA2A1VU;S6fA4S37S78VX;Vs;S6fA3S37S76Vs;S6fA2S37S0S65S0R1VX;A3S36S3dS1A1S4dS6fR2A2S3cS1S6S3eS0A1M0G0A2A2A3F_;Fx;S37S74Vt4;S6fA2S37S36S3fS15A1SeS6fA1SeVt4;A1A3S0S3S3aS4eVX;S6fR2R1A4S4eS41S0Vg;VX;A3Vt4;R2R1A4A2Fa;Fq;A2A2A2A2A2A2").
    Proof using Cr4 HI HI4 HR2g HU HXz4 Hact HactU Hall HfrP HiP HkP Hlinks Hmem Hml0 HnU Hsc HscP Hu HuP UB4.
      pose proof (free_meta_spec (g :: X) None U t4 g
                    (fun r => Inv X None U (snd r) /\ same_but_metas_heads t4 (snd r) /\ (forall q a, usedX X (snd r) q a <-> usedX (g :: X) t4 q a) /\ ub_same t4 (snd r))
                    HI4 ltac:(left; reflexivity)) as T.
      specialize (T ltac:(intros s' HI5 Sb5 _ EU5 UB5; rewrite (remove_head_notin g X NXg) in HI5, EU5; cbn [snd]; auto)).
      destruct (itok_of_eq _ _ _ T free_meta_eq) as (HI5 & Sb5 & EU5 & UB5). cbn [snd] in HI5, Sb5, EU5, UB5.
      split; [exact HI5|]. split.
      { intros q a Hq. apply EU5 in Hq. destruct (Cr4 q a Hq) as (a3 & H3 & E3 & F3).
        destruct (corr_s3v q a3 H3) as (a0 & H0 & E0 & F0 & _). exists a0. split; [exact H0|]. split; congruence. }
      split; [eapply ub_same_trans; [exact ub_s3v | eapply ub_same_trans; [exact UB4 | exact UB5]]|].
      split.
      { intros x Hx. assert (Hxg : x <> g) by (intros ->; pose proof NXg as N; rewrite (proj2 (memb_In g X) Hx) in N; discriminate).
        pose proof (HXz4 x ltac:(right; exact Hx)) as Mx.
        destruct (st_free_meta_head t4) as [fm|] eqn:Hfh.
        - destruct (free_ring4 fm Hfh) as (hp & nx & pr2 & nx2 & M1 & M2 & N1 & N2 & _).
          unfold fgn_s5. rewrite (MT_fq_other t4 g fm hp nx pr2 nx2 Hfh M1 M2 N1 N2 x Hxg); [exact Mx | |]; intros ->; [rewrite M1 in Mx | rewrite M2 in Mx]; discriminate.
        - unfold fgn_s5. rewrite (MT_fq_empty_other t4 g x Hfh Hxg). exact Mx. }
      split.
      { destruct (st_free_meta_head t4) as [fm|] eqn:Hfh.
        - destruct (free_ring4 fm Hfh) as (hp & nx & pr2 & nx2 & M1 & M2 & N1 & N2 & _). exact (shape_fq_ring t4 g fm hp nx pr2 nx2 Hfh M1 M2 N1 N2).
        - exact (shape_fq_empty t4 g Hfh). }
      split; [destruct Sb5 as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&Erg&_); exact Erg|].
      exact EU5.
    Qed.
  End Finish.

End FreeGroupNested.
