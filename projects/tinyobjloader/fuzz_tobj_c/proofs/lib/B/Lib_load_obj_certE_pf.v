(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Corelib.Init.Datatypes"; "list"; "prod"; "nat"; "pair"; "bool"; "true"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "ldef"; "tblB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loopEf"; "ndE0f"; "ndXEf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@Corelib.Init.Logic"; "and"; "ex"; "eq"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "ndLE"; "ndXE"; "ndX0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD1"; "K_disp"; "bd_disp"; "La_errx"; "s_dispA"; "s_dispX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD_eqs"; "nd_d0"; "PhisD"; "V_ld"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loopE"; "K_loopE2"; "X_latchE2"; "K_afterE2"; "s_E"; "X_bodyE2"; "X_errxE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "JA"; "ok_frameKA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "mul"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_exits"; "K_afterE"; "X_bodyE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "X_latch7"; "X_latchE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_certE"; "cutsE2g"; "ndE0d"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "KU"; "bxK"; "bxN"; "bxS"; "bxV"; "bd_nn"; "bd_wpos"; "bsumK"; "bsumV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "phiK"; "wsub_id_on"; "JAF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_loopEf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_epiD1 Lib_load_obj_epiD_eqs Lib_load_obj_boxkit Lib_load_obj_certE.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma bd_disp_sums : ltac2:(tb__ "0|0|
S1S13S15S17S43S1fR1A2Z0A3S13S15S17S42S1fR1A2S32Z14S3bA2A3S13S40S1fR1A2S15S8S41S1fA1S9A3A2A2A2Frho;").
Proof.
  intros rho. unfold bd_disp, BIc. cbn [bsumV bsumK bi_v bi_k]. unfold bival. cbn [bi_f bi_c lfval]. split; [lia|]. split; [lia|].
  split; [|reflexivity]. unfold bd_nn. repeat constructor; unfold bival; cbn [bi_f bi_c lfval]; lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S4dS1S4SaQ40A1A1S4aOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S4cS0VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S17S48VCST;R1A2S13S30Z0R2A2S31R2S47A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S17S48VXGL;R1A2S13S30Z0R2A2S31R2S47A2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S4S5S5S17S17A2S17A2A1").

Variables BX BXL : bxt.
Hypothesis HBX : BXok_d 7 BX.
Hypothesis HBXL : BXok_d 7 BXL.
Hypothesis HBS : ltac2:(tb__ "0|0|
S30S3eVBXL;A1S3eVBX;A1A2").
Hypothesis HBN : ltac2:(tb__ "0|0|
S30S3dVBXL;A1S3dVBX;A1A2").
Hypothesis HBV : ltac2:(tb__ "0|0|
S30S3fVBX;A1S3fVBXL;A1A2").
Hypothesis HBK : ltac2:(tb__ "0|0|
S30S33S3cVBX;A1S32Z14S3bA2A2S3cVBXL;A1A2").
Variable rho0 : valuation.
Let P0 : ltac2:(tb__ "0|0|
S1OFr;") := ltac2:(tb__ "0|0|
S4bVCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S2eVAInv;VCST;VXGL;S34VKc;Vrho0;VP0;VFB;VFF;VBX;S2dVnd;Ac").
Let JAvL (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S2eVAInv;VCST;VXGL;S34VKc;Vrho0;VP0;VFB;VFF;VBXL;S2dVnd;Ac").
Let JAFvL (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S46VAInv;VCST;VXGL;S34VKc;Vrho0;VP0;VFB;VFF;VBXL;S2dVPhi;Vnd;Ad").

Lemma box_disp : ltac2:(tb__ "0|0|
S18S1S4SaQ40A1A1SfS3S0VJAvL;SdA1R4R3R2R1A6S3S0VJAv;S3aA1R5R4R3R2A6F_;Fw;Ftp;Frho;FL;").
Proof.
  intros L rho tp w Hw. destruct (BXok_d_pair _ BX HBX) as [V0 K0]. destruct (bd_disp_sums rho) as (SV & SK & Snn & Swp).
  apply (SPA_rebox AInv CST XGL NP Kc rho0 P0 FB FF PTrue BXL BX tvL frL [] bd_disp (AHead pH false) L rho tp w HBS HBN V0 K0 Swp); [|exact Hw].
  intros _ _. split; [exact Snn|]. rewrite SV, SK. cbn [bsumV bsumK]. unfold bxV, bxK in *. lia.
Qed.
Lemma land_dispA : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1SfS3S0VJAvL;SdA1S20R3R2R1A6S3S0VJAv;S23A1S1eS19R4S21A2R3R2A6F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hw. pose proof epiD1_checks_join as (_ & Ce & _ & Cid & _).
  pose proof certE_checks_disp as (_ & Cnp & Cnb & Ctv & Cfr & Cbd & Cam & _).
  exact (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc La_errx K_disp s_dispA ndE0d nd_d0 rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam
           (box_disp La_errx rho tp w Hw)).
Qed.
Lemma land_dispX : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1SfS3S0VJAvL;SdA1S2bR3R2R1A6S3S0VJAv;S23A1S1eS19R4S22A2R3R2A6F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hw. pose proof epiD1_checks_join as (_ & _ & Ce & _ & Cid & _).
  pose proof certE_checks_disp as (_ & _ & _ & _ & _ & _ & _ & _ & Cnp & Cnb & Ctv & Cfr & Cbd & Cam & _).
  exact (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc X_errxE2 K_disp s_dispX ndE0d nd_d0 rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam
           (box_disp X_errxE2 rho tp w Hw)).
Qed.

Lemma arr_latchf : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1SfS3S0VJAFvL;ScSeA2S27R3R2R1A6S14S1S1S13SbR1A1S3S0VJAvL;SdA1S26R1R4R3A6A2Lrho2;A2F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue tblB ndXEf X_latchE2 rho tp w Hw) as [HS HB].
  destruct (latch_absorbE2f AInv CST XGL ALA HCST HXGL Kc HKc FB FF BXL PTrue rho0 rho tp w HB HS) as (rho2 & HT & HS2 & _).
  exists rho2. split; [exact (tblL_ldef rho2 HT) | exact HS2].
Qed.
Lemma arr_latch2 : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1SfS3S0VJAFvL;ScS1cA2S27R3R2R1A6S14S1S1S13SbR1A1S3S0VJAvL;SdA1S26R1R4R3A6A2Lrho2;A2F_;Fw;Ftp;Frho;").
Proof. intros rho tp w Hw. exact (arr_latchf rho tp w (relaxF_latchE2 AInv CST XGL Kc FB FF BXL HBXL PTrue rho0 rho tp w Hw)). Qed.
Lemma arr_latch1 : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1SfS3S0VJAFvL;ScS1cA2S38R3R2R1A6S14S1S1S13SbR1A1S3S0VJAvL;SdA1S26R1R4R3A6A2Lrho2;A2F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue tblB ndXE X_latchE rho tp w Hw) as [HS HB].
  pose proof certE_checks_sE as (CB & _ & _).
  apply (arr_latch2 (rho_sub rho s_E) tp w). apply SPA_JAF_intro; [|exact (phi_sub V_B tblB tblB_reads s_E rho CB HB)].
  exact (relax_latchE AInv CST XGL ALA Kc HKc FB FF BXL PTrue rho0 rho tp w HS).
Qed.
Lemma arr_latch7 : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1SfS3S0VJAFvL;ScS1dA2S37R3R2R1A6S14S1S1S13SbR1A1S3S0VJAvL;SdA1S26R1R4R3A6A2Lrho2;A2F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue tblB ndX0 X_latch7 rho tp w Hw) as [HS HB].
  pose proof certE_checks_l7 as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam & CB).
  apply (arr_latch2 (rho_sub rho s_l7) tp w). apply SPA_JAF_intro; [|exact (phi_sub V_B tblB tblB_reads s_l7 rho CB HB)].
  exact (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BXL PTrue HKc X_latch7 X_latchE2 s_l7 ndX0 ndXE rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam HS).
Qed.
Lemma sE_ldef : ltac2:(tb__ "0|0|
S1SbR1A1SbS19R2S29A2A1F_;Frho;").
Proof. intros rho HL. pose proof certE_checks_sE as (_ & CL & _). exact (phi_sub V_ld ldef ldef_reads s_E rho CL HL). Qed.
Lemma arr_bodyE : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1SfS3S0VJAvL;S1bA1S36R3R2R1A6S3S0VJAvL;SdA1S2aS19R4S29A2R3R2A6F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hw. apply (JA_pot_drop segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue HBXL tvL frL [] pH).
  exact (relax_bodyE AInv CST XGL ALA Kc HKc FB FF BXL PTrue rho0 rho tp w Hw).
Qed.
Lemma arr_afterE : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1SfS3S0VJAvL;S1bA1S35R3R2R1A6S3S0VJAvL;SdA1S28S19R4S29A2R3R2A6F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hw. apply (JA_pot_drop segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue HBXL tvL frL [] pH).
  exact (relax_afterE AInv CST XGL ALA Kc HKc FB FF BXL PTrue rho0 rho tp w Hw).
Qed.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S2fS0VKc;Vok;A3").
Variable Q : assn.
Hypothesis KDISP_T : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1SbR2A1S11S0Vok;S3S0VJAv;S23A1S1eR3R2A5VQ;A4F_;Ftp;Frho;").

Lemma XD_T : ltac2:(tb__ "0|1|
S18S1aS12S1S4SaQ40A1A1M0SfS3S0VJAvL;SdA1R6R3R2R1A6S3S0VJAv;S23A1S1eS19R4R6A2R3R2A6F_;Fw;Ftp;Frho;S15S8S45S25R3A2S9A3S1G0S11S0Vok;S3S0VJAFvL;SbSdA2R7R2R1A5SfS16R6R1A1VQ;R1A1A2Lw;A4Ftp;Frho;F_;F_;FF;Fs;FL;").
Proof.
  intros L s F HL Hs rho tp. apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue ldef ok). intros HP.
  eapply triple_conseq; [intros w Hw; exact (HL rho tp w Hw) | intros w Hw; right; exact Hw |].
  apply KDISP_T. exact (phi_sub V_ld ldef ldef_reads s rho Hs HP).
Qed.

Lemma E3_T : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1SbR2A1S11S0Vok;S3S0VJAvL;SdA1S28R3R2A5VQ;A4F_;Ftp;Frho;").
Proof.
  intros rho tp HL. pose proof certE_checks_disp as (_ & _ & _ & _ & _ & _ & _ & CidA & _).
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue (phiK PhisD 0) ok ndE0f K_afterE2 rho tp Q HL).
  apply (cfg_sound_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BXL PTrue HKc PhisD PhisD_reads 300%nat cps_epi NP (map efdrop cutsE3) (map efdrop exitsE3) ok Q Hok
           (ejcertAF_jcertAF segs NP PhisD _ _ _ _ _ ecertE3_ok)); [|left; reflexivity].
  intros X ndX kX rho1 tp1 [E|[]]. injection E as <- <- <-.
  exact (XD_T La_errx s_dispA _ land_dispA CidA rho1 tp1).
Qed.

Lemma E2_T : ltac2:(tb__ "0|3|
S18S2cS6S5S17S2A2M0S1S4SaQ40A1A1S49S5S5S5S18S2cA2M1S6A2M2G0A2S7G2G0S7G1S6S7S18S2cR6R5A4R4A4R3A4S39A3S44S24R5R3A3S11S0Vok;S3S0VJAvL;R7A1R8R4R3A5VQ;A4F_;F_;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp Hin Hphi. pose proof certE_checks_disp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CidX).
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue (phiK PhisD k) ok nd T rho tp Q Hphi).
  apply (cfg_sound_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BXL PTrue HKc PhisD PhisD_reads 150%nat cps_loop NP (map efdrop cutsE2g) (map efdrop exitsE2g) ok Q Hok
           (ejcertAF_jcertAF segs NP PhisD _ _ _ _ _ ecertE2g_ok)); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 [E|[E|[]]]; injection E as <- <- <-.
  - apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue (phiK PhisD 0) ok). intros HP.
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (E3_T rho1 tp1 HP)].
  - exact (XD_T X_errxE2 s_dispX _ land_dispX CidX rho1 tp1).
Qed.

Lemma loopE_T : ltac2:(tb__ "0|0|
S4SaQ40A1A1S12SfR2R1A1S14S1S1S13SbR1A1S3S0VJAvL;SdA1S26R1R5R3A6A2Lrho2;A2F_;Fw;S11S0Vok;R2VQ;A4F_;FP;Ftp;").
Proof.
  intros tp P HP. eapply triple_conseq; [exact HP | intros w Hw; exact Hw |].
  apply triple_ex. intros rho2. apply triple_pure. intros HL.
  exact (E2_T K_loopE2 ndE0f 0%nat (RL, VLA 26 z0) rho2 tp ltac:(left; reflexivity) HL).
Qed.

Theorem errLf_T : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1S11S0Vok;S3S0VJAFvL;ScSeA2S27R2R1A5VQ;A4Ftp;Frho;").
Proof. intros rho tp. exact (loopE_T tp _ (arr_latchf rho tp)). Qed.
Theorem errL2_T : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1S11S0Vok;S3S0VJAFvL;ScS1cA2S27R2R1A5VQ;A4Ftp;Frho;").
Proof. intros rho tp. exact (loopE_T tp _ (arr_latch2 rho tp)). Qed.
Theorem errL1_T : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1S11S0Vok;S3S0VJAFvL;ScS1cA2S38R2R1A5VQ;A4Ftp;Frho;").
Proof. intros rho tp. exact (loopE_T tp _ (arr_latch1 rho tp)). Qed.
Theorem err7_T : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1S11S0Vok;S3S0VJAFvL;ScS1dA2S37R2R1A5VQ;A4Ftp;Frho;").
Proof. intros rho tp. exact (loopE_T tp _ (arr_latch7 rho tp)). Qed.
Theorem errB_T : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1SbR2A1S11S0Vok;S3S0VJAvL;S1bA1S36R3R2A5VQ;A4F_;Ftp;Frho;").
Proof.
  intros rho tp HL. eapply triple_conseq; [intros w Hw; exact (arr_bodyE rho tp w Hw) | intros w Hw; exact Hw |].
  exact (E2_T X_bodyE2 ndE0f 0%nat (RL, VLA 25 z0) _ tp ltac:(right; left; reflexivity) (sE_ldef rho HL)).
Qed.
Theorem errA_T : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1SbR2A1S11S0Vok;S3S0VJAvL;S1bA1S35R3R2A5VQ;A4F_;Ftp;Frho;").
Proof.
  intros rho tp HL. eapply triple_conseq; [intros w Hw; exact (arr_afterE rho tp w Hw) | intros w Hw; exact Hw |].
  exact (E3_T _ tp (sE_ldef rho HL)).
Qed.
End Safety.

Section Existence.
Variable Q : world -> Prop.
Hypothesis KDISP_E : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1SbR2A1S10S0S3S0VJAv;S23A1S1eR3R2A5VQ;A3F_;Ftp;Frho;").

Lemma XD_E : ltac2:(tb__ "0|1|
S18S1aSfOF_;S1S4SaQ40A1A1M0SfS3S0VJAvL;SdA1R6R3R2R1A6S3S0VJAv;S23A1S1eS19R4R6A2R3R2A6F_;Fw;Ftp;Frho;S15S8S45S25R3A2S9A3S1G0S10S0S3S0VJAFvL;SbSdA2R7R2R1A5SfS16R6R1A1VQ;R1A1A2Lw;A3Ftp;Frho;F_;F_;FF;Fs;FL;").
Proof.
  intros L s F HL Hs rho tp. apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue ldef). intros HP.
  eapply etriple_conseq; [intros w Hw; exact (HL rho tp w Hw) | intros w Hw; right; exact Hw |].
  apply KDISP_E. exact (phi_sub V_ld ldef ldef_reads s rho Hs HP).
Qed.

Lemma E3_E : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1SbR2A1S10S0S3S0VJAvL;SdA1S28R3R2A5VQ;A3F_;Ftp;Frho;").
Proof.
  intros rho tp HL. pose proof certE_checks_disp as (_ & _ & _ & _ & _ & _ & _ & CidA & _).
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue (phiK PhisD 0) ndE0f K_afterE2 rho tp Q HL).
  refine (cfg_complete_JAF_b segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BXL PTrue HKc PhisD PhisD_reads 300%nat cps_epi NP cutsE3 exitsE3 (fun _ w => Q w)
           (fun b b' w _ Hw => Hw) ecertE3_ok _ K_afterE2 ndE0f 0%nat (400, z0) rho tp _); [|left; reflexivity].
  intros X ndX kX rvX rho1 tp1 [E|[]]. injection E as <- <- <- <-.
  exact (XD_E La_errx s_dispA _ land_dispA CidA rho1 tp1).
Qed.

Lemma E2_E : ltac2:(tb__ "0|3|
S18S2cS6S5S17S2A2M0S1S4SaQ40A1A1S49S5S5S5S18S2cA2M1S6A2M2G0A2S7G2G0S7G1S6S7S18S2cR6R5A4R4A4R3A4S39A3S44S24R5R3A3S10S0S3S0VJAvL;R7A1R8R4R3A5VQ;A3F_;F_;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp Hin Hphi. pose proof certE_checks_disp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CidX).
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue (phiK PhisD k) nd T rho tp Q Hphi).
  refine (cfg_complete_JAF_b segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BXL PTrue HKc PhisD PhisD_reads 150%nat cps_loop NP cutsE2g exitsE2g (fun _ w => Q w)
           (fun b b' w _ Hw => Hw) ecertE2g_ok _ T nd k rv rho tp _); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 [E|[E|[]]]; injection E as <- <- <- <-.
  - apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue (phiK PhisD 0)). intros HP.
    eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (E3_E rho1 tp1 HP)].
  - exact (XD_E X_errxE2 s_dispX _ land_dispX CidX rho1 tp1).
Qed.

Lemma loopE_E : ltac2:(tb__ "0|0|
S4SaQ40A1A1SfOF_;SfR2R1A1S14S1S1S13SbR1A1S3S0VJAvL;SdA1S26R1R5R3A6A2Lrho2;A2F_;Fw;S10S0R2VQ;A3F_;FP;Ftp;").
Proof.
  intros tp P HP. eapply etriple_conseq; [exact HP | intros w Hw; exact Hw |].
  apply etriple_ex. intros rho2. apply etriple_pure. intros HL.
  exact (E2_E K_loopE2 ndE0f 0%nat (RL, VLA 26 z0) rho2 tp ltac:(left; reflexivity) HL).
Qed.

Theorem errLf_E : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1S10S0S3S0VJAFvL;ScSeA2S27R2R1A5VQ;A3Ftp;Frho;").
Proof. intros rho tp. exact (loopE_E tp _ (arr_latchf rho tp)). Qed.
Theorem errL2_E : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1S10S0S3S0VJAFvL;ScS1cA2S27R2R1A5VQ;A3Ftp;Frho;").
Proof. intros rho tp. exact (loopE_E tp _ (arr_latch2 rho tp)). Qed.
Theorem errL1_E : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1S10S0S3S0VJAFvL;ScS1cA2S38R2R1A5VQ;A3Ftp;Frho;").
Proof. intros rho tp. exact (loopE_E tp _ (arr_latch1 rho tp)). Qed.
Theorem err7_E : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1S10S0S3S0VJAFvL;ScS1dA2S37R2R1A5VQ;A3Ftp;Frho;").
Proof. intros rho tp. exact (loopE_E tp _ (arr_latch7 rho tp)). Qed.
Theorem errB_E : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1SbR2A1S10S0S3S0VJAvL;S1bA1S36R3R2A5VQ;A3F_;Ftp;Frho;").
Proof.
  intros rho tp HL. eapply etriple_conseq; [intros w Hw; exact (arr_bodyE rho tp w Hw) | intros w Hw; exact Hw |].
  exact (E2_E X_bodyE2 ndE0f 0%nat (RL, VLA 25 z0) _ tp ltac:(right; left; reflexivity) (sE_ldef rho HL)).
Qed.
Theorem errA_E : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1SbR2A1S10S0S3S0VJAvL;S1bA1S35R3R2A5VQ;A3F_;Ftp;Frho;").
Proof.
  intros rho tp HL. eapply etriple_conseq; [intros w Hw; exact (arr_afterE rho tp w Hw) | intros w Hw; exact Hw |].
  exact (E3_E _ tp (sE_ldef rho HL)).
Qed.
End Existence.
End Sum.
