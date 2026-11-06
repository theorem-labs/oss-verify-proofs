(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "prod"; "list"; "nat"; "bool"; "true"; "Some"; "fst"; "option"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "la_state"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "nd_below"; "JA"; "frozen"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "ss_next"; "ss_facts"; "sprop"; "agree_below"; "holds"; "sobj"; "sprop_below"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "ndA1"; "RL"; "VLA"; "z0"; "ndX0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "tblB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "efmeasA"; "phiK"; "JAF"; "phi_reads"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_disp"; "E_mf"; "E_mf0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_aus_pf.Sum"; "pure_ruleL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn"; "PhisV"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_aus"; "cutsU"; "E_u2"; "E_u20"; "T_u2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "X_latch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_b_warn"; "Pre_bw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_b_warn_H"; "Posts_bwH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nt.Lib_mat_find"; "Posts_mf"; "Pre_mf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf"; "frozen_stableH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@Stdlib.PArith.BinPos.Pos"; "le"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nt.Lib_mat_find OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_b_warn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_b_warn_H.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn Lib_load_obj_aus.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr MatFindAddr BWarnAddr LOAddr LOLAddr HVAddr.

Lemma PhisV_reads : ltac2:(tb__ "0|3|
S3dS1S2S10A1M0S17OF_;M1A2M2G2S31S7G0G1R1A3S9G0G1R1A3A2Lp;S3aA3").
Proof. constructor; [exact tblL_reads | constructor; [exact tblB_reads | constructor]]. Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S53S17S2S20Q40A1A1S4aOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S52SaVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
SfS49VCST;R1A2S33S35Z0R2A2S36R2S48A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
SfS49VXGL;R1A2S33S35Z0R2A2S36R2S48A2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2S1S1SfSfA2SfA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let P0 : ltac2:(tb__ "0|0|
S17OFr;") := ltac2:(tb__ "0|0|
S4cVCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S14VAInv;VCST;VXGL;S34VKc;Vrho0;VP0;VFB;VFF;VBX;S12Vnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S30VAInv;VCST;VXGL;S34VKc;Vrho0;VP0;VFB;VFF;VBX;S12VPhi;Vnd;Ad").

Let frozen_stable : ltac2:(tb__ "0|0|
S10S10S11S17S54S34R3A2S32S4S13R4R3A2S5A3S23SaR6S15VAInv;VCST;VXGL;S34VKc;Vrho0;VP0;VFB;VFF;VBX;S12R4R3AdA3F_;F_;Frho;Fnd;Fm;Fn;") := ltac2:(tb__ "0|0|
S4bVAInv;VCST;VXGL;VALA;S34VKc;VHKc;VFB;VFF;VBX;Vrho0;VP0;Ac").

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
SfS2S20Q40A1A1S29F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S22SbS17S2S20Q40A1A1S29S3dS1bS1dR3A1S1aScR4A1A1A3VTR;S21SaR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S29S29S29S2cR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_JAF : ltac2:(tb__ "0|0|
S17OF_;S11SbS17S2S20Q40A1A1S29R6R3A1VTR;S21SaVJAv;R6A1R5R4R3A5R2A2F_;VTR;S21SaVJAFv;R7R6A2R5R4R3A5R2A2F_;FQ;Ftp;Frho;FA;Fnd;FPhi;").

Definition pure_ruleL (Pre : axst) (Posts : list leafA) : Prop := ltac2:(tb__ "0|2|
SbS4dS2S1eA1M0S17S2S20Q40A1A1S11S29S32S8G0A1S50R7VPre;R6A3S6G0R5A2A3S32S4S4fR8VPre;R7R6S3eSdSbSeVPosts;A4A5S5A3S32S4S55S34S19ScR9A1A1A2S5A3S32S4S13S19ScRaA1A1R5A2S5A3S32S4S3cS1bS1fS19ScRbA1M1A1A1S1aG1A1A3S5A3SdS17S3bSdR2VPosts;A3S1cS19ScRfA1A1RcR2A3VTR;S21SaVJAv;RbA1S4eS1aScR10A1A1S51RfVPre;SeR4A1R10ReA5A2R3RcA5RaA2F_;F_;Frho';FL;VTR;S21SaVJAv;R8A1RdRaR9A5R7A2F_;F_;F_;F_;F_;F_;FQ;Fnd;Ftp;Frho;FR;Fs;FCl;").
Hypothesis PURE_mf : pure_ruleL Pre_mf Posts_mf.
Hypothesis PURE_da : pure_ruleL Pre_bw Posts_bwH.
Hypothesis CUTV : ltac2:(tb__ "0|5|
SbS11S3S1SfS18A2M0S17S2S20Q40A1A1M1SfG1S3bS1S1S1SbS11A2M2S3A2M3G0A2S0G3G0S0G2S3S0SbS11R8R7A4R6A4R5A4S3fA3S2fS3aR7R5A3S33S35Z0S2eS0G3G0S0G2S3S0SbS11RaR9A4R8A4R7A4R6A2M4A2S36G4R4A2A2VTR;S21SaVJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").

Lemma site_da : ltac2:(tb__ "0|2|
S17S2S20Q40A1A1S29S17S3dS1bS1dR4A1S1aScS40A1M0A1A3S1cS19G0A1R5R2A3VTR;S21SaVJAv;S24A1M1S42R3R5A5R4A2F_;F_;Frho';VTR;S21SaG1S41R4R3A5R2A2F_;FQ;Ftp;Frho;").
Proof.
  intros rho tp Q HK. pose proof aus_checks2 as (Cxf & Cent & Cchk & Cnp & Cnb & Cfb & CT0 & CB & CT & _).
  apply (TR_pre (SPA segs (JAv ndA1) E_u2 rho tp)). { intros w Hw. exact (SPA_axforms segs (JAv ndA1) xf_u2 rho E_u20 E_u2 tp w Cxf Hw). }
  apply TR_facts. intros HF.
  apply (PURE_da E_u2 s_u2 R_u2 rho tp ndA1 _ Cent Cchk Cnp Cnb Cfb).
  intros L rho' HL Hag. cbn [In Posts_bwH] in HL. destruct HL as [<-|[]]. cbn [la_state]. rewrite CT0.
  apply (TR_pre (SPA segs (JAv ndA1) T_u2 rho' tp)).
  { intros w Hw. rewrite <- CT. apply SPA_tidy. exact (SPA_axforms segs (JAv ndA1) (xfb_leaf (-96) T_u20) rho' T_u20 B_u2 tp w CB Hw). }
  exact (HK rho' HF Hag).
Qed.

Theorem arm_us : ltac2:(tb__ "0|2|
S17S2S20Q40A1A1M0G0VTR;S21SaVJAFv;S2dS24A2S37R3R2A5VFAM;S2eS0S1S1SbS11A2M1S3A2S1SfS18A2S0G1S3S0SbS11S37S24A4U1A4S0SfS18S25S26Z11S27A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI.
  pose proof aus_checks1 as (Cxf & Cent & Cchk & Cnp & Cnb & Cfb & CT0 & CB & CT & CVB).
  apply (TR_pre (SPA segs (JAv ndA1) E_u1 rho tp)). { intros w Hw. exact (SPA_axforms segs (JAv ndA1) xf_u1 rho E_mf E_u1 tp w Cxf Hw). }
  apply TR_facts. intros HF.
  apply (PURE_mf E_u1 s_u1 R_u1 rho tp ndA1 _ Cent Cchk Cnp Cnb Cfb).
  intros L rho' HL Hag. cbn [In Posts_mf] in HL. destruct HL as [<-|[]]. cbn [la_state]. rewrite CT0.
  apply (TR_pre (SPA segs (JAv ndA1) T_u1 rho' tp)).
  { intros w Hw. rewrite <- CT. apply SPA_tidy. exact (SPA_axforms segs (JAv ndA1) (xfb_leaf (-32) T_u10) rho' T_u10 B_u1 tp w CB Hw). }
  assert (HPHI' : tblB rho') by exact (phi_agree V_B tblB tblB_reads _ rho rho' CVB Hag HPHI).
  apply (CUTV T_u1 ndA1 1%nat (RL, VLA 10 z0) rho' tp); [left; reflexivity | exact HPHI' |].
  fact HF (SPUlt pI xLC) HiC. rewrite h_ult in HiC. fact HF (SPUle xLC vLEN) HcL. rewrite h_ule in HcL.
  fact HF (SPUle vLEN (SLit 67108864)) HL26. rewrite h_ule, uval_lit in HL26 by lia.
  apply (VLA_lt rho rho' 17 10 z0 E_mf T_u1 ndA1 ndA1 1%nat 1%nat);
    [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
Qed.

Theorem arm_us0 : ltac2:(tb__ "0|2|
S17S2S20Q40A1A1M0G0VTR;S21SaVJAFv;S2dS24A2S38R3R2A5VFAM;S2eS0S1S1SbS11A2M1S3A2S1SfS18A2S0G1S3S0SbS11S38S24A4U1A4S0SfS18S25S26Z11S27A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI.
  pose proof aus_checks0 as (Xe & Xid & Xnp & Xnb & Xtv & Xfr & Xbd & Xam & XV & W460 & W467).
  apply (TR_pre (SPA segs (JAFv tblB ndA1) E_mf (rho_sub rho s_u0) tp)).
  { intros w Hw.
    destruct (latch_exit AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc E_mf0 E_mf s_u0 ndA1 tvL (bdA A1) (AHead pH true) tblB V_B rho tp w
                tblB_reads Xe Xid Xnp Xnb Xtv Xfr Xbd Xam XV HPHI Hw) as [HP' Hw'].
    exact (SPA_JAF_intro segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB ndA1 E_mf _ tp w Hw' HP'). }
  rewrite <- (efmeasA_VLA_sub E_mf E_mf0 ndA1 ndA1 1%nat 1%nat RL 17 s_u0 rho W460 W467).
  exact (arm_us (rho_sub rho s_u0) tp tp0).
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S16SaVKc;Vok;A3").
Variable FAMQ : list word -> assn.
Hypothesis XLATCH : ltac2:(tb__ "0|1|
S17S2S20Q40A1A1M0G0S2bSaVok;S21SaVJAFv;S2dS28A2S43R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Lemma PURE_mf_T : ltac2:(tb__ "0|0|
S39S2bSaVok;A2S47S46A3").
Proof.
  intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
  apply (pure_callA segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HKc ALA ok Cl Pre_mf s R Posts_mf rho1 tp1 nd Q'); try assumption.
  intros rho2 tp2. apply mat_find_sum; [apply frozen_ok_frameA; exact Hok | apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
Qed.
Lemma PURE_da_T : ltac2:(tb__ "0|0|
S39S2bSaVok;A2S44S45A3").
Proof.
  intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
  apply (pure_callA segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HKc ALA ok Cl Pre_bw s R Posts_bwH rho1 tp1 nd Q'); try assumption.
  intros rho2 tp2. apply b_warn_sumH; [apply frozen_ok_frameA; exact Hok | apply (frozen_stable NPH (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
Qed.

Lemma CUTV_T : ltac2:(tb__ "0|5|
SbS11S3S1SfS18A2M0S17S2S20Q40A1A1M1SfG1S3bS1S1S1SbS11A2M2S3A2M3G0A2S0G3G0S0G2S3S0SbS11R8R7A4R6A4R5A4S3fA3S2fS3aR7R5A3S33S35Z0S2eS0G3G0S0G2S3S0SbS11RaR9A4R8A4R7A4R6A2M4A2S36G4R4A2A2S2bSaVok;S21SaVJAv;RaA1RbR7R6A5VFAMQ;R4A1A4F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi _.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads 200%nat cps_arm NP (map efdrop cutsU) (map efdrop exitsU) ok (FAMQ tp0') Hok
           (ejcertAF_jcertAF segs NP PhisV _ _ _ _ _ ecertU_ok)); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  cbn [exitsU In] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-; cbn [efdrop fst snd].
  -
    apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV 1)). intros HP1.
    apply (site_da (triple segs ok) (TRs_facts segs ok) (TRs_pre segs ok) PURE_da_T rho1 tp1). intros rho' HF Hag.
    pose proof aus_checks2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CVB & _).
    apply (reenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisV ok (map efdrop cutsU) T_u2 ndA1 1%nat (FAMQ tp0') rho' tp1); [right; left; reflexivity |].
    exact (phi_agree V_B tblB tblB_reads _ rho1 rho' CVB Hag HP1).
  - eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLATCH rho1 tp1 tp0')].
Qed.

Theorem arm_us_T : ltac2:(tb__ "0|1|
S17S2S20Q40A1A1M0G0S2bSaVok;S21SaVJAFv;S2dS24A2S37R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_us (triple segs ok) (fun _ tp0 => FAMQ tp0) (TRs_facts segs ok) (TRs_pre segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           PURE_mf_T CUTV_T rho tp tp0).
Qed.
Theorem arm_us0_T : ltac2:(tb__ "0|1|
S17S2S20Q40A1A1M0G0S2bSaVok;S21SaVJAFv;S2dS24A2S38R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_us0 (triple segs ok) (fun _ tp0 => FAMQ tp0) (TRs_facts segs ok) (TRs_pre segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           PURE_mf_T CUTV_T rho tp tp0).
Qed.
End Safety.

Section Existence.
Variable FAM : ltac2:(tb__ "0|0|
SfS2S20Q40A1A1S29F_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
SfSfS2S20Q40A1A1S2cS35R4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis XLATCH : ltac2:(tb__ "0|2|
S17S2S20Q40A1A1M0G0S2aSaS21SaVJAFv;S2dS28A2S43R3R2A5VFAM;S2eS0S1S1SbS11A2M1S3A2S1SfS18A2S0G1S3S0SbS11S43S28A4U1A4S0SfS18S25S26Z1S27A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").

Lemma PURE_mf_E : ltac2:(tb__ "0|0|
S39S2aSaA1S47S46A3").
Proof.
  intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
  apply (pure_callA_ex segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HKc ALA Cl Pre_mf s R Posts_mf rho1 tp1 nd Q'); try assumption.
  intros rho2 tp2. apply mat_find_sum_ex. apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
Qed.
Lemma PURE_da_E : ltac2:(tb__ "0|0|
S39S2aSaA1S44S45A3").
Proof.
  intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
  apply (pure_callA_ex segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HKc ALA Cl Pre_bw s R Posts_bwH rho1 tp1 nd Q'); try assumption.
  intros rho2 tp2. apply b_warn_sumH_ex. apply (frozen_stable NPH (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
Qed.

Lemma CUTV_E : ltac2:(tb__ "0|5|
SbS11S3S1SfS18A2M0S17S2S20Q40A1A1M1SfG1S3bS1S1S1SbS11A2M2S3A2M3G0A2S0G3G0S0G2S3S0SbS11R8R7A4R6A4R5A4S3fA3S2fS3aR7R5A3S33S35Z0S2eS0G3G0S0G2S3S0SbS11RaR9A4R8A4R7A4R6A2M4A2S36G4R4A2A2S2aSaS21SaVJAv;RaA1RbR7R6A5VFAM;R5R4A2A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi Hm.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) nd T rho tp _ Hphi).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (FAM_mono _ b tp0' w ltac:(apply Z.lt_le_incl; exact (proj2 Hm)) Hw) |].
  apply (cfg_complete_JAF_b segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads 200%nat cps_arm NP cutsU exitsU (fun b w => FAM b tp0' w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0' w Hb Hw) ecertU_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX. cbn [exitsU In] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-.
  -
    apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV 1)). intros HP1.
    apply (site_da (etriple segs) (TRe_facts segs) (TRe_pre segs) PURE_da_E rho1 tp1). intros rho' HF Hag.
    pose proof aus_checks2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CVB & _).
    eapply (ereenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisV cutsU T_u2 ndA1 1%nat (RL, VLA 5 z0));
      [right; left; reflexivity | exact (phi_agree V_B tblB tblB_reads _ rho1 rho' CVB Hag HP1) |].
    fact HF (SPUlt pI xLC) HiC. rewrite h_ult in HiC. fact HF (SPUle xLC vLEN) HcL. rewrite h_ule in HcL.
    fact HF (SPUle vLEN (SLit 67108864)) HL26. rewrite h_ule, uval_lit in HL26 by lia.
    apply (VLA_lt rho1 rho' 7 5 z0 E_u20 T_u2 ndA1 ndA1 1%nat 1%nat);
      [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
  - eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLATCH rho1 tp1 tp0')].
Qed.

Theorem arm_us_E : ltac2:(tb__ "0|2|
S17S2S20Q40A1A1M0G0S2aSaS21SaVJAFv;S2dS24A2S37R3R2A5VFAM;S2eS0S1S1SbS11A2M1S3A2S1SfS18A2S0G1S3S0SbS11S37S24A4U1A4S0SfS18S25S26Z11S27A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_us (etriple segs) FAM (TRe_facts segs) (TRe_pre segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           PURE_mf_E CUTV_E rho tp tp0).
Qed.
Theorem arm_us0_E : ltac2:(tb__ "0|2|
S17S2S20Q40A1A1M0G0S2aSaS21SaVJAFv;S2dS24A2S38R3R2A5VFAM;S2eS0S1S1SbS11A2M1S3A2S1SfS18A2S0G1S3S0SbS11S38S24A4U1A4S0SfS18S25S26Z11S27A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_us0 (etriple segs) FAM (TRe_facts segs) (TRe_pre segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           PURE_mf_E CUTV_E rho tp tp0).
Qed.
End Existence.
End Sum.

