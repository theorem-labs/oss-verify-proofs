(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "mslot"; "astate"; "ameta"; "am_sc"; "am_next"; "MUsed"; "am_prev"; "IRet"; "itree"; "nontrivial_free"; "MFree"; "am_last"; "bit"; "frame"; "free_meta"; "links_of"; "ones"; "am_avail"; "with_links"; "am_freed"; "am_mem"; "st_free_meta_head"; "FGroup"; "am_set_links"; "fkind"; "fr_kind"; "nth_slot"; "okay_to_free"; "slot_start"; "ss_fr"; "am_maplen"; "bind"; "find_frame"; "ibind"; "mupdate"; "ret"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "iff"; "@Corelib.Init.Datatypes"; "Some"; "option"; "prod"; "pair"; "None"; "bool"; "nat"; "unit"; "false"; "cons"; "fst"; "S"; "tt"; "list"; "true"; "andb"; "nil"; "option_map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "MT"; "active_hd"; "memb"; "usedX"; "Inv"; "keys"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zomb"; "zomb"; "zmetas"; "zmeta"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost"; "dq_post"; "nmask"; "or_post"; "fq_post"; "fgd_post"; "fgm_post"; "q0_mid"; "q1_s3"; "q2_s3"; "fgd_res"; "fgm_res"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtRealN.Wrap"; "REALPOST"; "NTF_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "upd_meta"; "ub_same"; "ucontrib"; "@Stdlib.Lists.List"; "In"; "NoDup"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtNested"; "fgn_s3"; "amP'"; "fgn_s3v"; "fgn_s2"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtRealN.RealFinish"; "fin_real"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree"; "corr"; "fneed"; "nf_post"; "@Corelib.Init.Peano"; "le"; "@Corelib.Lists.ListDef"; "map"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfFrame MallocWfRings MallocWfGeom MallocWfFree ImageDelta
  TryAvailPost FreeNtPost FreeNtNested Zomb FreeNtReal.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma free_meta_run g t : ltac2:(tb__ "0|5|
S0S25S2bS0A1M0S16Vt;A1S2aS0R1A2M1A3S26S27S25S0R2Vg;A3A1S28S1S1S28S0S0S26S25S2bS1A1M2S3cVt;R4A2S2aS1R2A2A3S26S25G0S34G0G0S10R2A1A3G1A3S26S27S25S0R1Vg;A3A1S27S25G2S3cVt;R1A2S2eS1A1A3A1A2A2A2Lhp;A2Lxf;A2A2F_;Ffm;S25S9S2S2cS31S2A2M3A2SfVg;Vt;A2S8S2G3S2dS31S2S36S49S53Vg;SbS2eS0A1M4G4A2Vt;A3Vg;A2A4A3A3F_;").
Proof.
  intros Hring. unfold free_meta. rewrite (bind_eq _ _ t tt _ (setslot_eq t g (MFree None None))).
  apply queue_free_eq; [apply MT_upd_same|].
  intros fm Hfm. rewrite head_upd_meta in Hfm. destruct (Hring fm Hfm) as (NE & xf & hp & Mf & El & NEh & Mh).
  split; [exact NE|]. exists xf, hp. rewrite (MT_upd_other g _ t fm NE), (MT_upd_other g _ t hp NEh). auto.
Qed.

Section FgnEq.
  Variables (X : list sptr) (U : Z -> Z) (s : astate) (g : sptr) (am : ameta) (i : Z).
  Hypothesis HI : ltac2:(tb__ "0|0|
S40VX;S2aS2cS0S42A2S2dS0S42Vg;Vi;A4A2VU;Vs;A4").
  Hypothesis Hu : ltac2:(tb__ "0|0|
S3fVX;Vs;Vg;Vam;A4").
  Hypothesis HU : forall c, 0 <= U c.
  Hypothesis HR2g : ltac2:(tb__ "0|2|
S27S25S2cS2bS0A1M0G0A2S2dG0G0S7Vam;A1S5Vam;A1A4S2dG0G0S2eS0A1M1G1A4A3A1S27S25G0S3dVs;S4Vam;A1A2S2aS0Vg;A2A3A1S27S25S42S14Vam;A1Z0A3A1F_;F_;").
  Hypothesis Hall : ltac2:(tb__ "0|0|
S25S42S5dS47Vam;A1SdVi;A1A2S11ScVam;A1A1A3").
  Hypothesis Hsc : 0 <= am_sc am < 48.
  Hypothesis Hml0 : am_maplen am = 0.
  Hypothesis Hlinks : ltac2:(tb__ "0|2|
S0S25S2bS0A1M0S5Vam;A1S2aS0R1A2A3S27S25S0R2Vg;A3A1S28S0S0S28S1S1S28S1S1S26S25G0S7Vam;A1S2aS0R3A2A3S26S27S25S0R3Vg;A3A1S26S25S2bS1A1M1S3cVs;R3A2S2aS1R2A2A3S25G1S3cS53R3S13R2S34G0G0S10R2A1A3S2aS0R6A2A3Vs;A3R6A2S2aS1R1A2A3A2A2A2Lxn;A2Lxp;A2Lp;A2F_;F_;Fn;").
  Hypothesis HnU : ltac2:(tb__ "0|0|
S0S25S2bS0A1S5Vam;A1S2aS0R1A2A3S28S3S3S25S2bS1A1S3cVs;R3A2S2aS1S6R1A1A2A3Lan;A2F_;Fn;").
  Hypothesis Hact : ltac2:(tb__ "0|1|
S0S3S25S2bS0A1M0S5Vam;A1S2aS0R2A2A3S27S25S0R3Vg;A3A1S25G0S3dVs;S4Vam;A1A2S2aS0Vg;A2A3S25S2bS1A1S3cS46Vs;Vg;Vam;A3R5A2S2aS1S6R4A1A2A3S25S42S12R5A1Z0A3F_;F_;F_;F_;Fan;Fn;").
  Hypothesis HactU : ltac2:(tb__ "0|1|
S0S25S2bS0A1M0S5Vam;A1S2aS0R1A2A3S27S25S0R2Vg;A3A1S25G0S3dVs;S4Vam;A1A2S2aS0Vg;A2A3S28S3S3S25S2bS1A1S3cS46Vs;Vg;Vam;A3R5A2S2aS1S6R1A1A2A3Lan;A2F_;F_;F_;Fn;").
  Variables (gP : sptr) (amP : ameta) (iP : Z) (frP : frame).
  Hypothesis HuP : ltac2:(tb__ "0|0|
S3fVX;Vs;VgP;VamP;A4").
  Hypothesis HiP : ltac2:(tb__ "0|0|
S26S5cZ0ViP;A2S5cViP;ScVamP;A1A2A2").
  Hypothesis HfrP : ltac2:(tb__ "0|0|
S25S2bSeA1S1eS1bVamP;ViP;A2A1S2aSeVfrP;A2A3").
  Hypothesis HkP : ltac2:(tb__ "0|0|
S25S19S1aVfrP;A1S17A3").
  Hypothesis Hmem : ltac2:(tb__ "0|0|
S25S0S15Vam;A1S1dVamP;ViP;A2A3").
  Hypothesis HscP : ltac2:(tb__ "0|0|
S5eS4Vam;A1S4VamP;A1A2").

  Let s2 : astate := ltac2:(tb__ "0|0|
S5bVs;Vg;Vam;A3").
  Let s3 : astate := ltac2:(tb__ "0|0|
S58Vs;Vg;Vam;VgP;VamP;ViP;A6").

  Lemma Mg0 : ltac2:(tb__ "0|0|
S25S2bS1A1S3cVs;Vg;A2S2aS1S6Vam;A1A2A3"). Proof using Hu. exact (proj1 (usedX_MT _ _ _ _ Hu)). Qed.
  Lemma okay0 : ltac2:(tb__ "0|0|
S25S2fS1cVs;Vg;Vam;A3S38A3").
  Proof using Hml0. unfold okay_to_free. rewrite Hml0, Z.eqb_refl. destruct ((48 <=? am_sc am) || (stride_of am <? class_size (am_sc am)))%bool; reflexivity. Qed.

  Lemma find_frame2 : ltac2:(tb__ "0|2|
S25S9S2S2cS2cS0S42A2M0S2A2M1A2S21S15Vam;A1Vs2;A2S8S2G1S2dG0S2S2dS0S42VgP;ViP;A4Vs2;A4A3A3").
  Proof using HI HR2g HU Hact HactU Hall HfrP HiP HkP Hlinks Hmem Hml0 HnU Hsc HscP Hu HuP.
    destruct (s2_facts_model X U s g am i HI Hu HU HR2g Hall Hsc Hml0 Hlinks HnU Hact HactU amP iP Hmem HscP) as (HI2 & _).
    pose proof (HuP2 X U s g am i HI Hu HR2g Hall Hsc Hml0 Hlinks HnU Hact HactU gP amP iP HuP Hmem HscP) as HuP2'.
    unfold find_frame. rewrite (bind_eq _ _ s2 s2 s2 (get_eq s2)).
    assert (EP : am_mem am = frame_ptr amP iP frP).
    { rewrite Hmem. unfold frame_ptr. rewrite (fu_off X (Some (g, i)) U s gP amP iP frP HI HuP HiP HfrP HkP), Z.mul_0_r.
      unfold padd, slot_start. destruct (am_mem amP); cbn. f_equal. lia. }
    rewrite EP. change (st_metas s2) with (st_metas (fgn_s2 s g am)).
    rewrite (find_frame_in_spec (g :: X) None U (fgn_s2 s g am) HI2 gP amP iP frP HuP2' HiP HfrP). reflexivity.
  Qed.

  Theorem fgn_eq fuel : ltac2:(tb__ "0|3|
S25S9S2S2cS2bS2cS30S42A2A1M0S2A2M1A2M2SaS35Vfuel;A1Vg;Vi;Vs;A4S22S2G1G1SaVfuel;VgP;ViP;Vs3;A4G1G1G2Lr;R1G0S2S20S31G0SfVg;A1S31S24G0R3A2L_;R1A5Ls4;Lmi;X2cx1Lr;A5A3").
  Proof using HI HR2g HU Hact HactU Hall HfrP HiP HkP Hlinks Hmem Hml0 HnU Hsc HscP Hu HuP s2.
    pose proof (fgm_dq_eq X U s g am i HI Hu HR2g Hsc Hlinks HnU Hact HactU) as DQ.
    pose proof (MT_s1_g X s g am Hu HR2g Hlinks HnU Hact HactU) as M1.
    pose proof (MgP2 X U s g am i HI Hu HR2g Hall Hsc Hml0 Hlinks HnU Hact HactU gP amP iP HuP Hmem HscP) as MP2.
    cbn fix beta iota delta [nontrivial_free].
    rewrite (bind_eq _ _ s am s (getm_eq s g am Mg0)). rewrite (bind_eq _ _ s s s (get_eq s)). cbn zeta.
    fold (FreeNtPost.nmask am). rewrite Hall, Z.eqb_refl, okay0. cbn [andb].
    rewrite (bind_eq _ _ s tt (fgm_s1 s g am) DQ).
    rewrite (bind_eq _ _ (fgm_s1 s g am) _ (fgm_s1 s g am) (getm_eq (fgm_s1 s g am) g _ M1)).
    replace (am_sc match am_next am with Some _ => am_set_links None None am | None => am end) with (am_sc am) by (destruct (am_next am); reflexivity).
    replace (am_last match am_next am with Some _ => am_set_links None None am | None => am end) with (am_last am) by (destruct (am_next am); reflexivity).
    replace (am_maplen match am_next am with Some _ => am_set_links None None am | None => am end) with (am_maplen am) by (destruct (am_next am); reflexivity).
    replace (am_mem match am_next am with Some _ => am_set_links None None am | None => am end) with (am_mem am) by (destruct (am_next am); reflexivity).
    replace (am_sc am <? 48) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite (bind_eq _ _ (fgm_s1 s g am) tt s2) by (unfold s2, fgn_s2, fgm_s2; apply set_usage_of_eq).
    rewrite Hml0. cbn [Z.eqb negb].
    unfold bind at 1. f_equal.
    - rewrite (bind_eq _ _ s2 _ s2 find_frame2). cbn [fst snd].
      rewrite (bind_eq _ _ s2 amP s2 (getm_eq s2 gP amP MP2)).
      rewrite (bind_eq _ _ s2 tt s2) by (unfold mcheck, slot_is_group; rewrite HfrP, HkP; reflexivity).
      apply (bind_eq (forget_frame gP iP) (fun _ => nontrivial_free fuel gP iP) s2 tt s3).
      unfold forget_frame. rewrite (bind_eq _ _ s2 amP s2 (getm_eq s2 gP amP MP2)). exact (setm_eq s2 gP _).
  Qed.

  Corollary fgn_result fuel r t4 t5 : ltac2:(tb__ "0|4|
S25S9S2S2cS2bS2cS30S42A2A1M0S2A2M1A2M2SaVfuel;VgP;ViP;Vs3;A4S8S2G1S2dG0S2Vr;Vt4;A4A3A3S25S9S2S2cS31S2A2M3A2SfVg;Vt4;A2S8S2G3S2dS31S2S36Vt5;A4A3A3S25G2SaS35Vfuel;A1Vg;Vi;Vs;A4S8S2G1S2dG0S2Vr;Vt5;A4A3A3F_;F_;").
  Proof using HI HR2g HU Hact HactU Hall HfrP HiP HkP Hlinks Hmem Hml0 HnU Hsc HscP Hu HuP s2. intros E4 E5. rewrite fgn_eq, E4. cbn [ibind]. rewrite (bind_eq _ _ t4 tt t5 E5). reflexivity. Qed.
End FgnEq.

Lemma zmetas_notin X g l : ltac2:(tb__ "0|1|
S27S56S0Vg;S65S2cS0S1A2M0S0S34S0S1A2Vl;A4A3A1S25S37G0A1S44S33S0Vg;VX;A3Vl;A2S44VX;Vl;A2A3F_;").
Proof.
  induction l as [|[q x] l IH]; cbn; intros Hn; [reflexivity|].
  unfold zmeta at 1 2. rewrite memb_cons. destruct (sptr_eqb q g) eqn:E.
  - exfalso. apply sptr_eqb_eq in E. apply Hn. left. exact E.
  - cbn. f_equal. apply IH. intros Hin. apply Hn. right. exact Hin.
Qed.
Lemma zmetas_cons_upd X g l : ltac2:(tb__ "0|3|
S57S0S65S2cS0S1A2M0S0S34S0S1A2Vl;A4M1A2S56S0Vg;G1A3S25S37G0A1S44S33S0Vg;VX;A3Vl;A2S23S44VX;Vl;A2Vg;SbS2eS0A1M2G2A2A3A3F_;F_;").
Proof.
  induction l as [|[q x] l IH]; cbn; intros ND Hin; [destruct Hin|].
  inversion ND as [|q0 l0 Hq Hl]; subst.
  rewrite (sptr_eqb_sym g q). unfold zmeta at 1 2. rewrite memb_cons.
  destruct (sptr_eqb q g) eqn:E; cbn.
  - apply sptr_eqb_eq in E. subst q. f_equal. apply zmetas_notin. exact Hq.
  - f_equal. apply IH; [exact Hl|]. destruct Hin as [->|Hin]; [rewrite sptr_eqb_refl in E; discriminate | exact Hin].
Qed.
Lemma zomb_cons X g t : ltac2:(tb__ "0|2|
S57S0S41Vt;A1M0A2S56S0Vg;G0A3S25S2S43S33S0Vg;VX;A3Vt;A2S53Vg;SbS2eS0A1M1G1A2S43VX;Vt;A2A3A3F_;F_;").
Proof. intros ND Hk. unfold upd_meta, zomb, keys in *. destruct t; cbn -[zmetas mupdate] in *. rewrite (zmetas_cons_upd X g _ ND Hk). reflexivity. Qed.

Lemma corr_zomb X a b : ltac2:(tb__ "0|0|
S29S61VX;Va;Vb;A3S61VX;S43VX;Va;A2S43VX;Vb;A2A3A2").
Proof.
  unfold corr. split; intros H q am Hq.
  - apply (proj1 (usedX_zomb X b q am)) in Hq. destruct (H q am Hq) as (a0 & H0 & E). exists a0. split; [apply (proj2 (usedX_zomb X a q a0)); exact H0 | exact E].
  - destruct (H q am (proj2 (usedX_zomb X b q am) Hq)) as (a0 & H0 & E). exists a0. split; [apply (proj1 (usedX_zomb X a q a0)); exact H0 | exact E].
Qed.
Lemma ucontrib_zmeta X m x : ltac2:(tb__ "0|3|
S25S37S2cS2cS0S42A2M0G0A2M1A1M2S55Vm;S3bS1S1S45VX;Vm;A2Vx;A4A2S2fG2L_;S3eVm;VX;A2S3aG1A1S55Vm;Vx;A2X2fx2A3").
Proof. unfold zmeta. destruct (memb m X), x as [x0|]; cbn; try reflexivity; destruct x0; reflexivity. Qed.
Lemma ub_same_zomb X a b : ltac2:(tb__ "0|0|
S54Va;Vb;A2S54S43VX;Va;A2S43VX;Vb;A2A2F_;").
Proof.
  intros (ext & K & E1 & E2). exists ext. rewrite !keys_zomb. split; [exact K|]. split.
  - intros m Hm. rewrite MT_zomb, ucontrib_zmeta. destruct (memb m X); [reflexivity | exact (E1 m Hm)].
  - intros q Hq. rewrite !MT_zomb, !ucontrib_zmeta. destruct (memb q X); [reflexivity | exact (E2 q Hq)].
Qed.

Section RealNested.
  Variables (X : list sptr) (U : Z -> Z) (sr : astate) (g : sptr) (am : ameta) (i : Z).
  Let s : astate := zomb X sr.
  Hypothesis HIr : ltac2:(tb__ "0|0|
S40VX;S2aS2cS0S42A2S2dS0S42Vg;Vi;A4A2VU;Vsr;A4").
  Hypothesis Hu : ltac2:(tb__ "0|0|
S3fVX;Vs;Vg;Vam;A4").
  Hypothesis HU : forall c, 0 <= U c.
  Hypothesis HR2g : ltac2:(tb__ "0|2|
S27S25S2cS2bS0A1M0G0A2S2dG0G0S7Vam;A1S5Vam;A1A4S2dG0G0S2eS0A1M1G1A4A3A1S27S25G0S3dVs;S4Vam;A1A2S2aS0Vg;A2A3A1S27S25S42S14Vam;A1Z0A3A1F_;F_;").
  Hypothesis Hall : ltac2:(tb__ "0|0|
S25S42S5dS47Vam;A1SdVi;A1A2S11ScVam;A1A1A3").
  Hypothesis Hsc : 0 <= am_sc am < 48.
  Hypothesis Hml0 : am_maplen am = 0.
  Hypothesis Hlinks : ltac2:(tb__ "0|2|
S0S25S2bS0A1M0S5Vam;A1S2aS0R1A2A3S27S25S0R2Vg;A3A1S28S0S0S28S1S1S28S1S1S26S25G0S7Vam;A1S2aS0R3A2A3S26S27S25S0R3Vg;A3A1S26S25S2bS1A1M1S3cVs;R3A2S2aS1R2A2A3S25G1S3cS53R3S13R2S34G0G0S10R2A1A3S2aS0R6A2A3Vs;A3R6A2S2aS1R1A2A3A2A2A2Lxn;A2Lxp;A2Lp;A2F_;F_;Fn;").
  Hypothesis HnU : ltac2:(tb__ "0|0|
S0S25S2bS0A1S5Vam;A1S2aS0R1A2A3S28S3S3S25S2bS1A1S3cVs;R3A2S2aS1S6R1A1A2A3Lan;A2F_;Fn;").
  Hypothesis HpU : ltac2:(tb__ "0|0|
S0S25S2bS0A1S7Vam;A1S2aS0R1A2A3S28S3S3S25S2bS1A1S3cVs;R3A2S2aS1S6R1A1A2A3Lap;A2F_;Fp;").
  Hypothesis Hact : ltac2:(tb__ "0|1|
S0S3S25S2bS0A1M0S5Vam;A1S2aS0R2A2A3S27S25S0R3Vg;A3A1S25G0S3dVs;S4Vam;A1A2S2aS0Vg;A2A3S25S2bS1A1S3cS46Vs;Vg;Vam;A3R5A2S2aS1S6R4A1A2A3S25S42S12R5A1Z0A3F_;F_;F_;F_;Fan;Fn;").
  Hypothesis HactU : ltac2:(tb__ "0|1|
S0S25S2bS0A1M0S5Vam;A1S2aS0R1A2A3S27S25S0R2Vg;A3A1S25G0S3dVs;S4Vam;A1A2S2aS0Vg;A2A3S28S3S3S25S2bS1A1S3cS46Vs;Vg;Vam;A3R5A2S2aS1S6R1A1A2A3Lan;A2F_;F_;F_;Fn;").
  Variables (gP : sptr) (amP : ameta) (iP : Z) (frP : frame).
  Hypothesis HuP : ltac2:(tb__ "0|0|
S3fVX;Vs;VgP;VamP;A4").
  Hypothesis HiP : ltac2:(tb__ "0|0|
S26S5cZ0ViP;A2S5cViP;ScVamP;A1A2A2").
  Hypothesis HfrP : ltac2:(tb__ "0|0|
S25S2bSeA1S1eS1bVamP;ViP;A2A1S2aSeVfrP;A2A3").
  Hypothesis HkP : ltac2:(tb__ "0|0|
S25S19S1aVfrP;A1S17A3").
  Hypothesis Hmem : ltac2:(tb__ "0|0|
S25S0S15Vam;A1S1dVamP;ViP;A2A3").
  Hypothesis HscP : ltac2:(tb__ "0|0|
S5eS4Vam;A1S4VamP;A1A2").

  Lemma ngX : ltac2:(tb__ "0|0|
S25S2fS3eVg;VX;A2S32A3"). Proof using Hu. exact (proj2 (usedX_MT _ _ _ _ Hu)). Qed.
  Lemma ngPX : ltac2:(tb__ "0|0|
S25S2fS3eVgP;VX;A2S32A3"). Proof using HuP. exact (proj2 (usedX_MT _ _ _ _ HuP)). Qed.
  Lemma nnX n : ltac2:(tb__ "0|0|
S25S2bS0A1S5Vam;A1S2aS0Vn;A2A3S25S2fS3eVn;VX;A2S32A3F_;").
  Proof using HnU. intros En. destruct (HnU n En) as [an M]. apply (MT_virt_notX X sr n _ M). discriminate. Qed.
  Lemma npX p : ltac2:(tb__ "0|0|
S25S2bS0A1S7Vam;A1S2aS0Vp;A2A3S25S2fS3eVp;VX;A2S32A3F_;").
  Proof using HpU. intros Ep. destruct (HpU p Ep) as [ap M]. apply (MT_virt_notX X sr p _ M). discriminate. Qed.
  Lemma nHu_r : ltac2:(tb__ "0|0|
S3fVX;Vsr;Vg;Vam;A4"). Proof using Hu. exact (proj1 (usedX_zomb X sr g am) Hu). Qed.
  Lemma nHuP_r : ltac2:(tb__ "0|0|
S3fVX;Vsr;VgP;VamP;A4"). Proof using HuP. exact (proj1 (usedX_zomb X sr gP amP) HuP). Qed.
  Lemma nHR2g_r : ltac2:(tb__ "0|2|
S27S25S2cS2bS0A1M0G0A2S2dG0G0S7Vam;A1S5Vam;A1A4S2dG0G0S2eS0A1M1G1A4A3A1S27S25G0S3dVsr;S4Vam;A1A2S2aS0Vg;A2A3A1S27S25S42S14Vam;A1Z0A3A1F_;F_;").
  Proof using HR2g. intros H1 H2. apply HR2g; [exact H1|]. unfold s. rewrite active_hd_zomb. exact H2. Qed.
  Lemma nMTr q : ltac2:(tb__ "0|0|
S25S2fS3eVq;VX;A2S32A3S25S2bS1A1S3cVsr;Vq;A2S3cVs;Vq;A2A3F_;"). Proof using . intros B. unfold s. rewrite (MT_zomb_notX X sr q B). reflexivity. Qed.
  Lemma ndq_r : ltac2:(tb__ "0|0|
S25S2S46Vs;Vg;Vam;A3S43VX;S46Vsr;Vg;Vam;A3A2A3"). Proof using HnU HpU Hu. unfold s. apply dq_post_zomb; [exact ngX | exact nnX | exact npX]. Qed.
  Lemma nHlinks_r : ltac2:(tb__ "0|2|
S0S25S2bS0A1M0S5Vam;A1S2aS0R1A2A3S27S25S0R2Vg;A3A1S28S0S0S28S1S1S28S1S1S26S25G0S7Vam;A1S2aS0R3A2A3S26S27S25S0R3Vg;A3A1S26S25S2bS1A1M1S3cVsr;R3A2S2aS1R2A2A3S25G1S3cS53R3S13R2S34G0G0S10R2A1A3S2aS0R6A2A3Vsr;A3R6A2S2aS1R1A2A3A2A2A2Lxn;A2Lxp;A2Lp;A2F_;F_;Fn;").
  Proof using Hlinks HnU HpU.
    intros n En Hng. destruct (Hlinks n En Hng) as (p & xp & xn & Ep & Hpg & Mp & Mn). exists p, xp, xn.
    split; [exact Ep|]. split; [exact Hpg|]. split; [rewrite (nMTr p (npX p Ep)); exact Mp|].
    rewrite <- (MT_zomb_notX X _ n (nnX n En)), <- (upd_meta_zomb X sr p _ (npX p Ep)). exact Mn.
  Qed.
  Lemma nHnU_r : ltac2:(tb__ "0|0|
S0S25S2bS0A1S5Vam;A1S2aS0R1A2A3S28S3S3S25S2bS1A1S3cVsr;R3A2S2aS1S6R1A1A2A3Lan;A2F_;Fn;").
  Proof using HnU. intros n En. destruct (HnU n En) as [an M]. exists an. rewrite (nMTr n (nnX n En)). exact M. Qed.
  Lemma nHpU_r : ltac2:(tb__ "0|0|
S0S25S2bS0A1S7Vam;A1S2aS0R1A2A3S28S3S3S25S2bS1A1S3cVsr;R3A2S2aS1S6R1A1A2A3Lap;A2F_;Fp;").
  Proof using HpU. intros p Ep. destruct (HpU p Ep) as [ap M]. exists ap. rewrite (nMTr p (npX p Ep)). exact M. Qed.
  Lemma nHact_r : ltac2:(tb__ "0|1|
S0S3S25S2bS0A1M0S5Vam;A1S2aS0R2A2A3S27S25S0R3Vg;A3A1S25G0S3dVsr;S4Vam;A1A2S2aS0Vg;A2A3S25S2bS1A1S3cS46Vsr;Vg;Vam;A3R5A2S2aS1S6R4A1A2A3S25S42S12R5A1Z0A3F_;F_;F_;F_;Fan;Fn;").
  Proof using Hact HnU HpU Hu.
    intros n an En Hng Hhd M. apply (Hact n an En Hng); [unfold s; rewrite active_hd_zomb; exact Hhd|].
    rewrite ndq_r, (MT_zomb_notX X _ n (nnX n En)). exact M.
  Qed.
  Lemma nHactU_r : ltac2:(tb__ "0|1|
S0S25S2bS0A1M0S5Vam;A1S2aS0R1A2A3S27S25S0R2Vg;A3A1S25G0S3dVsr;S4Vam;A1A2S2aS0Vg;A2A3S28S3S3S25S2bS1A1S3cS46Vsr;Vg;Vam;A3R5A2S2aS1S6R1A1A2A3Lan;A2F_;F_;F_;Fn;").
  Proof using HactU HnU HpU Hu.
    intros n En Hng Hhd. destruct (HactU n En Hng ltac:(unfold s; rewrite active_hd_zomb; exact Hhd)) as [an M]. exists an.
    rewrite ndq_r, (MT_zomb_notX X _ n (nnX n En)) in M. exact M.
  Qed.

  Let s3r : astate := ltac2:(tb__ "0|0|
S58Vsr;Vg;Vam;VgP;VamP;ViP;A6").

  Theorem s3r_X x : ltac2:(tb__ "0|0|
S56S0Vx;VX;A3S25S2bS1A1S3cVs3r;Vx;A2S3cVsr;Vx;A2A3F_;").
  Proof using HR2g Hact HactU Hlinks HnU HpU Hu HuP iP.
    intros Hx. assert (Bx : memb x X = true) by (apply memb_In; exact Hx).
    assert (NE : forall q, memb q X = false -> q <> x) by (intros q Hq ->; rewrite Bx in Hq; discriminate).
    unfold s3r, fgn_s3, fgn_s2, fgm_s2. rewrite (MT_upd_other gP _ _ x (fun E => NE gP ngPX (eq_sym E))).
    change (MT (fgm_s1 sr g am) x = MT sr x). unfold fgm_s1.
    rewrite (MT_act_other sr g am nHR2g_r nHlinks_r nHnU_r nHact_r nHactU_r (dq_post sr g am) x) by (intros n En; exact (fun E => NE n (nnX n En) (eq_sym E))).
    apply (MT_dq_other sr g am nHR2g_r nHlinks_r nHnU_r nHpU_r nHact_r nHactU_r x).
    - exact (fun E => NE g ngX (eq_sym E)).
    - intros n En. exact (fun E => NE n (nnX n En) (eq_sym E)).
    - intros p Ep. exact (fun E => NE p (npX p Ep) (eq_sym E)).
  Qed.

  Theorem fgn_real fuel r t4 t5 : ltac2:(tb__ "0|4|
S25S9S2S2cS2bS2cS30S42A2A1M0S2A2M1A2M2SaVfuel;VgP;ViP;Vs3r;A4S8S2G1S2dG0S2Vr;Vt4;A4A3A3S25S9S2S2cS31S2A2M3A2SfVg;Vt4;A2S8S2G3S2dS31S2S36Vt5;A4A3A3S25G2SaS35Vfuel;A1Vg;Vi;Vsr;A4S8S2G1S2dG0S2Vr;Vt5;A4A3A3F_;F_;").
  Proof using HIr HR2g HU Hact HactU Hall HfrP HiP HkP Hlinks Hmem Hml0 HnU HpU Hsc HscP Hu HuP. exact (fgn_result X U sr g am i HIr nHu_r HU nHR2g_r Hall Hsc Hml0 nHlinks_r nHnU_r nHact_r nHactU_r gP amP iP frP nHuP_r HiP HfrP HkP Hmem HscP fuel r t4 t5). Qed.

  Theorem s3r_facts : ltac2:(tb__ "0|1|
S26S40S33S0Vg;VX;A3M0S2aS2cS0S42A2S2dS0S42VgP;ViP;A4A2VU;Vs3r;A4S3fG0Vs3r;VgP;S59VamP;ViP;A2A4A2").
  Proof using HIr HR2g HU Hact HactU Hall HfrP HiP Hlinks Hmem Hml0 HnU HpU Hsc HscP Hu HuP. exact (s3_facts_model X U sr g am i HIr nHu_r HU nHR2g_r Hall Hsc Hml0 nHlinks_r nHnU_r nHact_r nHactU_r gP amP iP frP nHuP_r HiP HfrP Hmem HscP). Qed.

  Lemma fgn_s3_zomb : ltac2:(tb__ "0|0|
S25S2S58Vs;Vg;Vam;VgP;VamP;ViP;A6S43VX;Vs3r;A2A3").
  Proof using HnU HpU Hu HuP.
    unfold s3r, fgn_s3, fgn_s2, fgm_s2, fgm_s1, s.
    rewrite (dq_post_zomb X sr g am ngX nnX npX), (act_post_zomb X g am nnX), usage_of_zomb, st_usage_zomb, set_usage_zomb.
    apply upd_meta_zomb. exact ngPX.
  Qed.
  Theorem s3v_zomb : ltac2:(tb__ "0|0|
S25S2S5aVs;Vg;Vam;VgP;VamP;ViP;A6S43S33S0Vg;VX;A3Vs3r;A2A3").
  Proof using HIr HR2g HU Hact HactU Hall HfrP HiP Hlinks Hmem Hml0 HnU HpU Hsc HscP Hu HuP.
    unfold fgn_s3v. rewrite fgn_s3_zomb. symmetry. destruct s3r_facts as [HI3 _]. apply zomb_cons.
    - exact (proj1 (inv_keys HI3)).
    - exact (proj1 (inv_X HI3 g ltac:(left; reflexivity))).
  Qed.
End RealNested.

Section RealFinish.
  Variables (X : list sptr) (U : Z -> Z) (g : sptr) (t4r : astate).
  Hypothesis HI4r : ltac2:(tb__ "0|0|
S40S33S0Vg;VX;A3S2eS2cS0S42A2A1VU;Vt4r;A4").
  Hypothesis gX : ltac2:(tb__ "0|0|
S25S2fS3eVg;VX;A2S32A3").
  Let t4 : astate := ltac2:(tb__ "0|0|
S43S33S0Vg;VX;A3Vt4r;A2").
  Definition fin_real : astate := ltac2:(tb__ "0|1|
S49S53Vg;SbS2eS0A1M0G0A2Vt4r;A3Vg;A2").

  Lemma g_key4 : In g (keys t4r). Proof using HI4r. exact (proj1 (inv_X HI4r g ltac:(left; reflexivity))). Qed.
  Lemma ND4r : NoDup (keys t4r). Proof using HI4r. exact (proj1 (inv_keys HI4r)). Qed.
  Lemma ring4r fm : ltac2:(tb__ "0|1|
S25S2bS0A1S16Vt4r;A1S2aS0Vfm;A2A3S28S0S0S28S0S0S28S0S0S28S0S0S26S25S2bS1A1M0S3cVt4r;Vfm;A2S2aS1SbS2aS0R4A2S2aS0R3A2A2A2A3S26S25G0S3cVt4r;R4A2S2aS1SbS2aS0R2A2S2aS0R1A2A2A2A3S26S27S25S0Vfm;Vg;A3A1S26S27S25S0R4Vg;A3A1S26S25S2fS3eVfm;VX;A2S32A3S25S2fS3eR4VX;A2S32A3A2A2A2A2A2Lnx2;A2Lpr2;A2Lnx;A2Lhp;A2F_;").
  Proof using HI4r.
    intros Hfh. destruct (free_ring_head (g :: X) None U t4r HI4r fm Hfh) as (hp & nx & pr2 & nx2 & M1 & M2 & X1 & X2 & _).
    rewrite memb_cons in X1, X2. apply Bool.orb_false_iff in X1 as [X1a X1b]. apply Bool.orb_false_iff in X2 as [X2a X2b].
    apply sptr_eqb_neq in X1a. apply sptr_eqb_neq in X2a. exists hp, nx, pr2, nx2. auto 10.
  Qed.
  Theorem free_meta_real : ltac2:(tb__ "0|1|
S25S9S2S2cS31S2A2M0A2SfVg;Vt4r;A2S8S2G0S2dS31S2S36S60A4A3A3").
  Proof using HI4r.
    apply free_meta_run. intros fm Hfh. destruct (ring4r fm Hfh) as (hp & nx & pr2 & nx2 & M1 & M2 & N1 & N2 & _).
    split; [exact N1|]. exists (MFree (Some hp) (Some nx)), hp. split; [exact M1|]. split; [reflexivity|]. split; [exact N2|]. rewrite M2. discriminate.
  Qed.
  Theorem fin_real_X x : ltac2:(tb__ "0|0|
S56S0Vx;VX;A3S25S2bS1A1S3cS60Vx;A2S3cVt4r;Vx;A2A3F_;").
  Proof using HI4r gX.
    intros Hx. assert (Bx : memb x X = true) by (apply memb_In; exact Hx).
    unfold fin_real. rewrite (fq_post_X X _ g x gX).
    - apply MT_upd_other. intros ->. rewrite Bx in gX. discriminate.
    - intros fm Hfh. rewrite head_upd_meta in Hfh. destruct (ring4r fm Hfh) as (hp & nx & pr2 & nx2 & M1 & M2 & N1 & N2 & B1 & B2).
      split; [exact B1|]. intros xf hp0 Mf El. rewrite (MT_upd_other g _ t4r fm N1), M1 in Mf. injection Mf as <-. cbn in El. injection El as <-. exact B2.
    - exact Bx.
  Qed.
  Theorem fin_real_zomb : ltac2:(tb__ "0|0|
S25S2S43VX;S60A2S49Vt4;Vg;A2A3").
  Proof using HI4r gX.
    unfold fin_real, t4. rewrite (zomb_cons X g t4r ND4r g_key4), (upd_meta_zomb X t4r g _ gX). symmetry. apply fq_post_zomb; [exact gX|].
    intros fm Hfh. rewrite head_upd_meta in Hfh. destruct (ring4r fm Hfh) as (hp & nx & pr2 & nx2 & M1 & M2 & N1 & N2 & B1 & B2).
    split; [exact B1|]. intros xf hp0 Mf El. rewrite (MT_upd_other g _ t4r fm N1), M1 in Mf. injection Mf as <-. cbn in El. injection El as <-. exact B2.
  Qed.
End RealFinish.

Section Wrap.
  Variables (X : list sptr) (U : Z -> Z) (sr s : astate) (g : sptr) (am : ameta) (i : Z).
  Hypothesis Hzs : ltac2:(tb__ "0|0|
S25S2Vs;S43VX;Vsr;A2A3").
  Hypothesis HIr : ltac2:(tb__ "0|0|
S40VX;S2aS2cS0S42A2S2dS0S42Vg;Vi;A4A2VU;Vsr;A4").
  Hypothesis Hu : ltac2:(tb__ "0|0|
S3fVX;Vs;Vg;Vam;A4").
  Hypothesis HU : forall c, 0 <= U c.
  Hypothesis HR2g : ltac2:(tb__ "0|2|
S27S25S2cS2bS0A1M0G0A2S2dG0G0S7Vam;A1S5Vam;A1A4S2dG0G0S2eS0A1M1G1A4A3A1S27S25G0S3dVs;S4Vam;A1A2S2aS0Vg;A2A3A1S27S25S42S14Vam;A1Z0A3A1F_;F_;").

  Definition NTF_EQ (r : option (nat * Z)) (sr' : astate) : Prop := ltac2:(tb__ "0|2|
S30S64S62S4Vam;A1A1R1A2S25S9S2S2cS2bS2cS30S42A2A1M0S2A2M1A2SaR2Vg;Vi;Vsr;A4S8S2G1S2dG0S2Vr;Vsr';A4A3A3F_;FF;").

  Definition REALPOST (r : option (nat * Z)) (s' sr' : astate) : Prop := ltac2:(tb__ "0|0|
S26S52Vr;Vsr';A2S26S25S2Vs';S43VX;Vsr';A2A3S26S40VX;S2eS2cS0S42A2A1VU;Vsr';A4S26S61VX;Vsr;Vsr';A3S26S54Vsr;Vsr';A2S0S56S0R1VX;A3S25S2bS1A1S3cVsr';R2A2S3cVsr;R2A2A3F_;Fx;A2A2A2A2A2").

  Lemma realpost_of (r : option (nat * Z)) (post : astate -> astate) : ltac2:(tb__ "0|6|
S30S26S25S9S2S2cS2bS2cS30S42A2A1M0S2A2M1A2SaS35R1A1M2Vg;Vi;Vsr;A4S8S2G1S2dG0S2Vr;Vpost;Vsr;A1M3A4M4A3A3S25S2S43VX;G3A2Vpost;S43VX;Vsr;A2A1M5A3A2Ffuel;S30S64S62S4Vam;A1A1G2A2S63VX;VU;Vsr;G4A4F_;Ffuel;S0S56S0R1VX;A3S25S2bS1A1S3cG3R2A2S3cVsr;R2A2A3F_;Fx;S51Vr;G5G3A3F_;F_;F_;").
  Proof using .
    intros E N XK. pose proof (fneed_pos (am_sc am)) as P.
    destruct (N (fneed (am_sc am) - 1)%nat ltac:(lia)) as (I1 & C1 & U1 & _). cbn [fst snd] in I1, C1, U1.
    split; [|split; [symmetry; exact (proj2 (E 0%nat)) | auto]].
    intros F HF. destruct F as [|F']; [lia|]. exact (proj1 (E F')).
  Qed.

  Section Else.
    Hypothesis Helse : ltac2:(tb__ "0|0|
S25S2fS39S5fS5dS47Vam;A1SdVi;A1A2S11ScVam;A1A1A2S1cVs;Vg;Vam;A3A2S32A3").
    Theorem or_realW : ltac2:(tb__ "0|0|
S27S25S42S47Vam;A1Z0A3A1S51S2eS2cS30S42A2A1S48Vg;Vi;Vs;Vam;A4S48Vg;Vi;Vsr;Vam;A4A3F_;").
    Proof using HIr HR2g HU Helse Hu Hzs. intros Hm. subst s. apply realpost_of; [intros fuel; exact (or_real X sr g am i Hu Helse fuel Hm)| |intros x Hx; exact (or_X X sr g am i Hu sr am x Hx)].
      intros fuel HF. exact (nf_real X U sr g am i HIr Hu HU HR2g fuel _ (proj1 (or_real X sr g am i Hu Helse fuel Hm)) HF). Qed.
    Theorem qg_realW : ltac2:(tb__ "0|0|
S25S42S47Vam;A1Z0A3S25S2bS0A1S3dVs;S4Vam;A1A2S2aS0Vg;A2A3S51S2eS2cS30S42A2A1S48Vg;Vi;Vs;Vam;A4S48Vg;Vi;Vsr;Vam;A4A3F_;F_;").
    Proof using HIr HR2g HU Helse Hu Hzs. intros Hm Hhd. subst s. apply realpost_of; [intros fuel; exact (qg_real X U sr g am i HIr Hu Helse fuel Hm Hhd)| |intros x Hx; exact (or_X X sr g am i Hu sr am x Hx)].
      intros fuel HF. exact (nf_real X U sr g am i HIr Hu HU HR2g fuel _ (proj1 (qg_real X U sr g am i HIr Hu Helse fuel Hm Hhd)) HF). Qed.
    Theorem q0_realW : ltac2:(tb__ "0|4|
S25S42S47Vam;A1Z0A3S25S2bS0A1M0S3dVs;S4Vam;A1A2S2eS0A1M1A3S25G0S7Vam;A1G1A3S25G0S5Vam;A1G1A3S51S2eS2cS30S42A2A1S48Vg;Vi;S4cVs;Vg;Vam;A3S18S2aS0Vg;A2M2G2Vam;A3M3A4S48Vg;Vi;S4cVsr;Vg;Vam;A3G3A4A3F_;F_;F_;F_;").
    Proof using HIr HR2g HU Helse Hu Hzs. intros Hm Hhd Hp Hn. subst s.
      apply (realpost_of None (fun t => or_post g i (q0_mid t g am) (am_set_links (Some g) (Some g) am))); [intros fuel; exact (q0_real X U sr g am i HIr Hu Helse fuel Hm Hhd Hp Hn)| |intros x Hx; exact (q0_X X sr g am i Hu x Hx)].
      intros fuel HF. exact (nf_real X U sr g am i HIr Hu HU HR2g fuel _ (proj1 (q0_real X U sr g am i HIr Hu Helse fuel Hm Hhd Hp Hn)) HF). Qed.
    Variables (h : sptr) (ah : ameta).
    Hypothesis Hhd : ltac2:(tb__ "0|0|
S25S2bS0A1S3dVs;S4Vam;A1A2S2aS0Vh;A2A3").
    Hypothesis Hhg : h <> g.
    Hypothesis Mh : ltac2:(tb__ "0|0|
S25S2bS1A1S3cVs;Vh;A2S2aS1S6Vah;A1A2A3").
    Hypothesis Hp : am_prev am = None.
    Hypothesis Hn : am_next am = None.
    Theorem q1_realW : ltac2:(tb__ "0|2|
S25S42S47Vam;A1Z0A3S25S2bS0A1S7Vah;A1S2aS0Vh;A2M0A3S51S2eS2cS30S42A2A1S48Vg;Vi;S4dVs;Vg;Vam;Vh;Vah;A5S18G0G0Vam;A3M1A4S48Vg;Vi;S4dVsr;Vg;Vam;Vh;Vah;A5G1A4A3F_;F_;").
    Proof using HIr HR2g HU Helse Hhd Hhg Hn Hp Hu Hzs Mh. intros Hm Hhp. subst s.
      apply (realpost_of None (fun t => or_post g i (q1_s3 t g am h ah) (am_set_links (Some h) (Some h) am))); [intros fuel; exact (q1_real X U sr g am i HIr Hu Helse h ah Hhd Hhg Mh Hp Hn fuel Hm Hhp)| |intros x Hx; exact (q1_X X sr g am i Hu h ah Mh x Hx)].
      intros fuel HF. exact (nf_real X U sr g am i HIr Hu HU HR2g fuel _ (proj1 (q1_real X U sr g am i HIr Hu Helse h ah Hhd Hhg Mh Hp Hn fuel Hm Hhp)) HF). Qed.
    Variables (t : sptr) (at_ : ameta).
    Hypothesis Htg : t <> g.
    Hypothesis Hth : t <> h.
    Hypothesis Mt : ltac2:(tb__ "0|0|
S25S2bS1A1S3cVs;Vt;A2S2aS1S6Vat_;A1A2A3").
    Theorem q2_realW : ltac2:(tb__ "0|2|
S25S42S47Vam;A1Z0A3S25S2bS0A1S7Vah;A1S2aS0Vt;A2M0A3S51S2eS2cS30S42A2A1S48Vg;Vi;S4eVs;Vg;Vam;Vh;Vah;Vt;Vat_;A7S18G0S2aS0Vh;A2Vam;A3M1A4S48Vg;Vi;S4eVsr;Vg;Vam;Vh;Vah;Vt;Vat_;A7G1A4A3F_;F_;").
    Proof using HIr HR2g HU Helse Hhd Hhg Hn Hp Htg Hth Hu Hzs Mh Mt. intros Hm Hhp. subst s.
      apply (realpost_of None (fun u => or_post g i (q2_s3 u g am h ah t at_) (am_set_links (Some t) (Some h) am))); [intros fuel; exact (q2_real X U sr g am i HIr Hu Helse h ah Hhd Hhg Mh Hp Hn t at_ Htg Hth Mt fuel Hm Hhp)| |intros x Hx; exact (q2_X X sr g am i Hu h ah Mh t at_ Mt x Hx)].
      intros fuel HF. exact (nf_real X U sr g am i HIr Hu HU HR2g fuel _ (proj1 (q2_real X U sr g am i HIr Hu Helse h ah Hhd Hhg Mh Hp Hn t at_ Htg Hth Mt fuel Hm Hhp)) HF). Qed.
  End Else.

  Theorem fgd_realW : ltac2:(tb__ "0|3|
S25S42S5dS47Vam;A1SdVi;A1A2S11ScVam;A1A1A3S25S42S4Vam;A1Z3fA3S25S2bS0A1M0S5Vam;A1S2eS0A1A3S27S25S42S1fVam;A1Z0A3A1S0S25G0S16Vs;A1S2aS0R1A2M1A3S26S27S25S0R2Vg;A3A1S28G0G0S28G0G0S28S0S0S26S25S2bS1A1M2S3cVs;R5A2S2aS1SbR3R2A2A2A3S26S25G0R3G1A3S26S27S25S0R1Vg;A3A1S26S27S25G2S3cVs;R1A2S2eS1A1A3A1S25S2fS3eR1VX;A2S32A3A2A2A2A2Lhp;A2Lnx;A2Lpr;A2A2F_;Ffm;S51S4fVam;A1S4aVs;Vg;A2S4aVsr;Vg;A2A3F_;F_;F_;F_;F_;").
  Proof using HIr HR2g HU Hu Hzs. intros Hall Hsc63 Hnx Hml HfrX. subst s.
    apply (realpost_of (fgd_res am) (fun t => fgd_post t g)); [intros fuel; exact (fgd_real X sr g am i Hu Hall Hsc63 Hnx Hml HfrX fuel)| |intros x Hx; exact (fgd_X X sr g am Hu HfrX x Hx)].
    intros fuel HF. exact (fgd_nf_real X U sr g am i HIr Hu HU HR2g Hall Hsc63 Hnx Hml HfrX fuel HF). Qed.

  Theorem fgm_realW : ltac2:(tb__ "0|f|
S25S42S5dS47Vam;A1SdVi;A1A2S11ScVam;A1A1A3S26S5cZ0M0S4Vam;A1M1A2S5eG1Z30A2A2S27S25S42S1fVam;A1G0A3A1S25S2fS1cVs;Vg;Vam;A3S38A3S0S25S2bS0A1M2S5Vam;A1M3S2aS0R1A2M4A3M5S27S25S0R2Vg;A3A1M6S28S0S0S28S1S1S28S1S1S26S25G2S7Vam;A1M7S2aS0R3A2A3S26S27S25S0R3Vg;A3A1M8S26S25S2bS1A1M9S3cVs;R3A2MaS2aS1R2A2A3S25G9S3cS53R3S13R2S34G2G2S10R2A1A3S2aS0R6A2A3Vs;A3R6A2S2aS1R1A2A3A2A2A2Lxn;A2Lxp;A2Lp;A2F_;F_;Fn;S0G5S28S3S3S25G9GaS2aS1S6R1A1A2MbA3McLan;A2F_;Fn;S0S25G2G7G4A3S28S3S3GcLap;A2F_;Fp;S0S3S25G2G3S2aS0R2A2A3G8S25G2S3dVs;G1A2S2aS0Vg;A2A3MdS25G9S3cS46Vs;Vg;Vam;A3R5A2MeS2aS1S6R4A1A2A3S25S42S12R5A1G0A3F_;F_;F_;F_;Fan;Fn;S0G5G6GdS28S3S3S25G9GeGbA3Lan;A2F_;F_;F_;Fn;S0S25G2S16Vs;A1G4A3S26G6S28S0S0S28G2G2S28G2G2S28G2G2S26S25G9S3cVs;R6A2S2aS1SbS2aS0R4A2R3A2A2A3S26S27S25S0R4Vg;A3A1S26S25G9S3cVs;R4A2S2aS1SbR2R1A2A2A3S25S2fS3eR4VX;A2S32A3A2A2A2Lnx2;A2Lpr2;A2Lnx;A2Lhp;A2A2F_;Ffm;S51S50Vam;A1S4bVs;Vg;Vam;A3S4bVsr;Vg;Vam;A3A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;").
  Proof using HIr HR2g HU Hu Hzs. intros Hall Hsc Hml Hok Hlinks HnU HpU Hact HactU HfrX. subst s.
    apply (realpost_of (fgm_res am) (fun t => fgm_post t g am)); [intros fuel; exact (fgm_real X U sr g am i HIr Hu HR2g Hall Hsc Hml Hok Hlinks HnU HpU Hact HactU HfrX fuel)| |intros x Hx; exact (fgm_X X sr g am Hu HR2g Hlinks HnU HpU Hact HactU HfrX x Hx)].
    intros fuel HF. exact (fgm_nf_real X U sr g am i HIr Hu HU HR2g Hall Hsc Hml Hok Hlinks HnU HpU Hact HactU HfrX fuel HF). Qed.

  Section Nested.
    Hypothesis Hall : ltac2:(tb__ "0|0|
S25S42S5dS47Vam;A1SdVi;A1A2S11ScVam;A1A1A3").
    Hypothesis Hsc : 0 <= am_sc am < 48.
    Hypothesis Hml0 : am_maplen am = 0.
    Hypothesis Hlinks : ltac2:(tb__ "0|2|
S0S25S2bS0A1M0S5Vam;A1S2aS0R1A2A3S27S25S0R2Vg;A3A1S28S0S0S28S1S1S28S1S1S26S25G0S7Vam;A1S2aS0R3A2A3S26S27S25S0R3Vg;A3A1S26S25S2bS1A1M1S3cVs;R3A2S2aS1R2A2A3S25G1S3cS53R3S13R2S34G0G0S10R2A1A3S2aS0R6A2A3Vs;A3R6A2S2aS1R1A2A3A2A2A2Lxn;A2Lxp;A2Lp;A2F_;F_;Fn;").
    Hypothesis HnU : ltac2:(tb__ "0|0|
S0S25S2bS0A1S5Vam;A1S2aS0R1A2A3S28S3S3S25S2bS1A1S3cVs;R3A2S2aS1S6R1A1A2A3Lan;A2F_;Fn;").
    Hypothesis HpU : ltac2:(tb__ "0|0|
S0S25S2bS0A1S7Vam;A1S2aS0R1A2A3S28S3S3S25S2bS1A1S3cVs;R3A2S2aS1S6R1A1A2A3Lap;A2F_;Fp;").
    Hypothesis Hact : ltac2:(tb__ "0|1|
S0S3S25S2bS0A1M0S5Vam;A1S2aS0R2A2A3S27S25S0R3Vg;A3A1S25G0S3dVs;S4Vam;A1A2S2aS0Vg;A2A3S25S2bS1A1S3cS46Vs;Vg;Vam;A3R5A2S2aS1S6R4A1A2A3S25S42S12R5A1Z0A3F_;F_;F_;F_;Fan;Fn;").
    Hypothesis HactU : ltac2:(tb__ "0|1|
S0S25S2bS0A1M0S5Vam;A1S2aS0R1A2A3S27S25S0R2Vg;A3A1S25G0S3dVs;S4Vam;A1A2S2aS0Vg;A2A3S28S3S3S25S2bS1A1S3cS46Vs;Vg;Vam;A3R5A2S2aS1S6R1A1A2A3Lan;A2F_;F_;F_;Fn;").
    Variables (gP : sptr) (amP : ameta) (iP : Z) (frP : frame).
    Hypothesis HuP : ltac2:(tb__ "0|0|
S3fVX;Vs;VgP;VamP;A4").
    Hypothesis HiP : ltac2:(tb__ "0|0|
S26S5cZ0ViP;A2S5cViP;ScVamP;A1A2A2").
    Hypothesis HfrP : ltac2:(tb__ "0|0|
S25S2bSeA1S1eS1bVamP;ViP;A2A1S2aSeVfrP;A2A3").
    Hypothesis HkP : ltac2:(tb__ "0|0|
S25S19S1aVfrP;A1S17A3").
    Hypothesis Hmem : ltac2:(tb__ "0|0|
S25S0S15Vam;A1S1dVamP;ViP;A2A3").
    Hypothesis HscP : ltac2:(tb__ "0|0|
S5eS4Vam;A1S4VamP;A1A2").
    Theorem fgn_realW fuel r t4 t5 : ltac2:(tb__ "0|4|
S25S9S2S2cS2bS2cS30S42A2A1M0S2A2M1A2M2SaVfuel;VgP;ViP;S58Vsr;Vg;Vam;VgP;VamP;ViP;A6A4S8S2G1S2dG0S2Vr;Vt4;A4A3A3S25S9S2S2cS31S2A2M3A2SfVg;Vt4;A2S8S2G3S2dS31S2S36Vt5;A4A3A3S25G2SaS35Vfuel;A1Vg;Vi;Vsr;A4S8S2G1S2dG0S2Vr;Vt5;A4A3A3F_;F_;").
    Proof using HIr HR2g HU Hact HactU Hall HfrP HiP HkP Hlinks Hmem Hml0 HnU HpU Hsc HscP Hu HuP Hzs. subst s. exact (fgn_real X U sr g am i HIr Hu HU HR2g Hall Hsc Hml0 Hlinks HnU HpU Hact HactU gP amP iP frP HuP HiP HfrP HkP Hmem HscP fuel r t4 t5). Qed.
    Theorem s3r_factsW : ltac2:(tb__ "0|2|
S26S40S33S0Vg;VX;A3M0S2aS2cS0S42A2S2dS0S42VgP;ViP;A4A2VU;S58Vsr;Vg;Vam;VgP;VamP;ViP;A6M1A4S3fG0G1VgP;S59VamP;ViP;A2A4A2").
    Proof using HIr HR2g HU Hact HactU Hall HfrP HiP Hlinks Hmem Hml0 HnU HpU Hsc HscP Hu HuP Hzs. subst s. exact (s3r_facts X U sr g am i HIr Hu HU HR2g Hall Hsc Hml0 Hlinks HnU HpU Hact HactU gP amP iP frP HuP HiP HfrP Hmem HscP). Qed.
    Theorem s3r_XW x : ltac2:(tb__ "0|0|
S56S0Vx;VX;A3S25S2bS1A1S3cS58Vsr;Vg;Vam;VgP;VamP;ViP;A6Vx;A2S3cVsr;Vx;A2A3F_;").
    Proof using HR2g Hact HactU Hlinks HnU HpU Hu HuP Hzs. subst s. eapply (s3r_X X sr g am); eauto. Qed.
    Theorem s3v_zombW : ltac2:(tb__ "0|0|
S25S2S5aVs;Vg;Vam;VgP;VamP;ViP;A6S43S33S0Vg;VX;A3S58Vsr;Vg;Vam;VgP;VamP;ViP;A6A2A3").
    Proof using HIr HR2g HU Hact HactU Hall HfrP HiP Hlinks Hmem Hml0 HnU HpU Hsc HscP Hu HuP Hzs. subst s. exact (s3v_zomb X U sr g am i HIr Hu HU HR2g Hall Hsc Hml0 Hlinks HnU HpU Hact HactU gP amP iP frP HuP HiP HfrP Hmem HscP). Qed.
  End Nested.
End Wrap.
