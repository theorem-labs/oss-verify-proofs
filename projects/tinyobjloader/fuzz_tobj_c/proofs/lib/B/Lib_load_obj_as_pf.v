(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "prod"; "nat"; "list"; "cons"; "bool"; "nil"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "JA"; "frozen"; "nd_below"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "holds"; "sprop"; "ss_facts"; "agree_below"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "@stdpp.bitvector.definitions"; "bv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "pow"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_aus_pf"; "pure_ruleL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "ndA1"; "RL"; "VLA"; "ndX0"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "efmeasA"; "phiK"; "JAF"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "vLEN"; "vBUF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_disp"; "E_nt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "tblB"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_as"; "T_s1f"; "cutsS"; "E_s2"; "E_si"; "K_s"; "K_sB"; "T_s2n"; "T_s2y"; "pEr"; "pSI"; "pSL"; "pST"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn"; "PhisV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "X_latch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_next_token"; "Posts_nt"; "Pre_nt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_int"; "Posts_si"; "Pre_si"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf"; "frozen_stableH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@Stdlib.PArith.BinPos.Pos"; "le"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.HideA.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_scan_int.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn Lib_load_obj_aus Lib_load_obj_aus_pf Lib_load_obj_as.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S53S11S3S1dQ40A1A1S4fOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S52S8VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S9S4eVCST;R1A2S22S1eZ0R2A2S1fR2S4dA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S9S4eVXGL;R1A2S22S1eZ0R2A2S1fR2S4dA2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S3S1S1S9S9A2S9A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let P0 : ltac2:(tb__ "0|0|
S11OFr;") := ltac2:(tb__ "0|0|
S51VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
SdVAInv;VCST;VXGL;S35VKc;Vrho0;VP0;VFB;VFF;VBX;ScVnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S33VAInv;VCST;VXGL;S35VKc;Vrho0;VP0;VFB;VFF;VBX;ScVPhi;Vnd;Ad").
Let frozen_stable : ltac2:(tb__ "0|0|
SaSaSbS11S54S35R3A2S23S5SfR4R3A2S7A3S1cS8R6SeVAInv;VCST;VXGL;S35VKc;Vrho0;VP0;VFB;VFF;VBX;ScR4R3AdA3F_;F_;Frho;Fnd;Fm;Fn;") := ltac2:(tb__ "0|0|
S50VAInv;VCST;VXGL;VALA;S35VKc;VHKc;VFB;VFF;VBX;Vrho0;VP0;Ac").

Lemma s1f_facts : ltac2:(tb__ "0|4|
S11S34S14S13R1A1S15S19S3bA1A1A3S22S1eZ1S2aR2S45A2M0A2S22S23S9S20S2aR2S46A2M1G0A2S2aR2S44A2M2A3S22S1eG2S2aR2S43A2A2S22S1eG2S2aR2S36A2A2S22S1eG1S21Z2Z28A2M3A2S1eG0G3A2A2A2A2A2A2F_;Fr;").
Proof.
  intros r HF.
  factz HF (SPUle (SLit 1) pSL) H1. rewrite uval_lit in H1 by lia.
  fact HF (SPEq (SAlu ALU_ADD pST pSL) pSI) H2. cbn [holds] in H2.
  factz HF (SPUle pSI pEr) H3. factz HF (SPUle pSI vLEN) H4.
  factz HF (SPUle pST (SLit 1099511627776)) H5. factz HF (SPUle pSL (SLit 1099511627776)) H6. rewrite uval_lit in H5, H6 by lia.
  assert (E2 : uval r (SAlu ALU_ADD pST pSL) = uval r pSI) by (unfold uval; rewrite H2; reflexivity).
  rewrite uval_add_small in E2 by lia. repeat split; lia.
Qed.

Lemma s1f_factsB : ltac2:(tb__ "0|0|
S11S34S14S13R1A1S15S19S3bA1A1A3S1eS20S2aR2S37A2S2aR2S36A2A2Z7fffff800000A2F_;Fr;").
Proof.
  intros r HF. factz HF (SPUle (SAlu ALU_ADD vBUF vLEN) (SLit 140737479966720)) H1. factz HF (SPUle vBUF (SLit 140737479966720)) H2. factz HF (SPUle vLEN (SLit 67108864)) H3.
  rewrite uval_lit in H1, H2, H3 by lia. rewrite uval_add_small in H1 by lia. exact H1.
Qed.

Lemma s_split : ltac2:(tb__ "0|0|
SbS11S3S1dQ40A1A1S29S1aS8VJAv;R4A1S3bR3R2R1A6S25S24S9S9S22S3aS9R1S4S9Z1S4S9Z2S4S9Z3S6S9A1A3A3A3A3S1aS8VJAv;R6A1S3fR1A1R5R4R3A6A2Lt;A2S1aS8VJAv;R5A1S40R4R3R2A6A2F_;Fw;Ftp;Frho;Fnd;").
Proof.
  intros nd rho tp w HS. pose proof (smatchA_facts segs _ _ _ _ (proj1 HS)) as HF.
  destruct (s1f_facts rho HF) as (H1 & H2 & H3 & H4 & H5 & H6). pose proof (s1f_factsB rho HF) as HBL. pose proof (uval_range rho vBUF) as RB. pose proof (uval_range rho pST) as RST. pose proof as_checks_split as (Cva & Cwf & CfB & Cft & _).
  pose proof (uval_range rho pEr) as RE. pose proof (uval_range rho vLEN) as RL'.
  destruct (Z_le_dec (uval rho pSL) 3) as [LE|GT].
  - left. set (t := uval rho pSL).
    assert (Ht : In t [1; 2; 3]) by (cbn; lia).
    exists t. split; [exact Ht|]. rewrite K_s_eq.
    assert (Hpin : SPA segs (JAv nd) (pinA T_s1f vSL (SLit t)) rho tp w).
    { apply (SPA_pin segs _ rho tp T_s1f vSL _ w); [| exact Cva | | exact HS].
      - exact (proj1 (forallb_forall _ _) Cwf t Ht).
      - apply bv_eq. change (uval rho pSL = uval rho (SLit t)). rewrite uval_lit by lia. reflexivity. }
    apply (SPA_refacts_JA segs _ rho _ _ tp w Hpin).
    + rewrite forallb_app, (proj1 (forallb_forall _ _) Cft t Ht). exact (swf_facts _ (proj1 (forallb_forall _ _) Cwf t Ht)).
    + intros tr md _ HFp. apply Forall_app. split; [|exact HFp]. constructor; [|constructor; [|constructor]]; apply (proj2 (h_ule _ _ _)).
      * unfold txt. rewrite uval_add_small by lia. rewrite uval_lit by lia. lia.
      * rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
  - right. rewrite K_sB_eq. apply (SPA_refacts_JA segs _ rho _ (sB_facts ++ ss_facts (ax_S T_s1f)) tp w HS).
    + rewrite forallb_app, CfB. cbn [andb]. pose proof as_checks1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CT & _). rewrite <- CT at 1.
      OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + intros tr md _ HFp. apply Forall_app. split; [|exact HFp]. unfold sB_facts.
      constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]; apply (proj2 (h_ule _ _ _)).
      * unfold txt. rewrite uval_add_small by lia. rewrite uval_lit by lia. lia.
      * rewrite uval_lit by lia. lia.
      * rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
      * rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
      * rewrite uval_add_small by lia. lia.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S9S3S1dQ40A1A1S26F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S1bS18S11S3S1dQ40A1A1S26S34S14S13R3A1S15S19R4A1A1A3VTR;S1aS8R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S26S26S26S29R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_JAF : ltac2:(tb__ "0|0|
S11OF_;SbS18S11S3S1dQ40A1A1S26R6R3A1VTR;S1aS8VJAv;R6A1R5R4R3A5R2A2F_;VTR;S1aS8VJAFv;R7R6A2R5R4R3A5R2A2F_;FQ;Ftp;Frho;FA;Fnd;FPhi;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S26OS26S29R4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis PURE_nt : ltac2:(tb__ "0|0|
S2bVAInv;VCST;VXGL;VKc;VFB;VFF;VBX;Vrho0;VTR;S4aS49Ab").
Hypothesis PURE_si : ltac2:(tb__ "0|0|
S2bVAInv;VCST;VXGL;VKc;VFB;VFF;VBX;Vrho0;VTR;S4cS4bAb").
Hypothesis CUTV : ltac2:(tb__ "0|5|
S18SbS2S1S9S12A2M0S11S3S1dQ40A1A1M1S9G1S3aS1S1S1S18SbA2M2S2A2M3G0A2S0G3G0S0G2S2S0S18SbR8R7A4R6A4R5A4S3cA3S32S47R7R5A3S22S1eZ0S31S0G3G0S0G2S2S0S18SbRaR9A4R8A4R7A4R6A2M4A2S1fG4R4A2A2VTR;S1aS8VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").

Lemma site_si : ltac2:(tb__ "0|4|
S11S3S1dQ40A1A1S26S11S34S14S13R4A1S15S19S3dA1M0A1M1A3S16S17G0A1M2R5R2A3VTR;S1aS8VJAv;S2cA1M3S41R3R5A5R4A2F_;F_;Frho';S11S34S14S13R5A1G1A3S16G2R6R2A3VTR;S1aS8G3S42R3R6A5R5A2F_;F_;Frho';VTR;S1aS8G3S3eR5R4A5R3A2F_;F_;FQ;Ftp;Frho;").
Proof.
  intros rho tp Q HKn HKy. pose proof as_checks2 as (_ & _ & Cxf & Cent & Cchk & Cnp & Cnb & Cfb & CTn0 & CTy0 & CBn & CTn & CBy & CTy & _).
  apply (TR_pre (SPA segs (JAv ndA1) E_s2 rho tp)). { intros w Hw. exact (SPA_axforms segs (JAv ndA1) (xf_si E_si) rho E_si E_s2 tp w Cxf Hw). }
  apply TR_facts. intros HF.
  apply (PURE_si E_s2 s_s2 R_s2 rho tp ndA1 _ Cent Cchk Cnp Cnb Cfb).
  intros L rho' HL Hag. cbn [In Lib_scan_int.Posts_si] in HL. destruct HL as [<-|[<-|[]]]; cbn [la_state].
  - rewrite CTn0. apply (TR_pre (SPA segs (JAv ndA1) T_s2n rho' tp)).
    { intros w Hw. rewrite <- CTn. apply SPA_tidy. exact (SPA_axforms segs (JAv ndA1) (xfb_s2 T_s2n0) rho' T_s2n0 B_s2n tp w CBn Hw). }
    exact (HKn rho' HF Hag).
  - rewrite CTy0. apply (TR_pre (SPA segs (JAv ndA1) T_s2y rho' tp)).
    { intros w Hw. rewrite <- CTy. apply SPA_tidy. exact (SPA_axforms segs (JAv ndA1) (xfb_s2 T_s2y0) rho' T_s2y0 B_s2y tp w CBy Hw). }
    exact (HKy rho' HF Hag).
Qed.

Theorem arm_s : ltac2:(tb__ "0|2|
S11S3S1dQ40A1A1M0G0VTR;S1aS8VJAFv;S39S2cA2S38R3R2A5VFAM;S31S0S1S1S18SbA2M1S2A2S1S9S12A2S0G1S2S0S18SbS38S2cA4U1A4S0S9S12S2dS2eZ11S30A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI.
  pose proof as_checks1 as (Cxf & Cent & Cchk & Cnp & Cnb & Cfb & CTn0 & CTf0 & CBn & CTn & CBf & CTf & CVB).
  apply (TR_pre (SPA segs (JAv ndA1) E_s1 rho tp)). { intros w Hw. exact (SPA_axforms segs (JAv ndA1) xf_s1 rho E_nt E_s1 tp w Cxf Hw). }
  apply TR_facts. intros HF.
  fact HF (SPUlt pI xLC) HiC. rewrite h_ult in HiC. fact HF (SPUle xLC vLEN) HcL. rewrite h_ule in HcL.
  fact HF (SPUle vLEN (SLit 67108864)) HL26. rewrite h_ule, uval_lit in HL26 by lia.
  apply (PURE_nt E_s1 s_s1 R_s1 rho tp ndA1 _ Cent Cchk Cnp Cnb Cfb).
  intros L rho' HL Hag.
  assert (HPHI' : tblB rho') by exact (phi_agree V_B tblB tblB_reads _ rho rho' CVB Hag HPHI).
  assert (HM : forall T' nd' k', 0 <= efmeasA (T', nd', k', (RL, VLA 10 z0)) rho' < efmeasA (E_nt, ndA1, 1%nat, (RL, VLA 17 z0)) rho).
  { intros T' nd' k'. apply (VLA_lt rho rho' 17 10 z0 E_nt T' ndA1 nd' 1%nat k');
      [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia]. }
  cbn [In OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_next_token.Posts_nt] in HL. destruct HL as [<-|[<-|[]]]; cbn [la_state].
  -
    rewrite CTn0. apply (TR_pre (SPA segs (JAv ndA1) T_s1n rho' tp)).
    { intros w Hw. rewrite <- CTn. apply SPA_tidy. exact (SPA_axforms segs (JAv ndA1) (xfb_s1 T_s1n0) rho' T_s1n0 B_s1n tp w CBn Hw). }
    apply (CUTV T_s1n ndA1 1%nat (RL, VLA 10 z0) rho' tp); [left; reflexivity | exact HPHI' | exact (HM T_s1n ndA1 1%nat)].
  -
    rewrite CTf0. apply (TR_pre (SPA segs (JAv ndA1) T_s1f rho' tp)).
    { intros w Hw. rewrite <- CTf. apply SPA_tidy. exact (SPA_axforms segs (JAv ndA1) (xfb_s1 T_s1f0) rho' T_s1f0 B_s1f tp w CBf Hw). }
    apply (TR_pre (fun w => exists c : option Z,
              (fun c w => match c with Some t => In t [1; 2; 3] /\ SPA segs (JAv ndA1) (K_s t) rho' tp w | None => SPA segs (JAv ndA1) K_sB rho' tp w end) c w)).
    { intros w Hw. destruct (s_split ndA1 rho' tp w Hw) as [(t & Ht & Hw')|Hw']; [exists (Some t); split; [exact Ht | exact Hw'] | exists None; exact Hw']. }
    apply TR_exw. intros [t|]; lazy beta iota.
    + apply (TR_pureP _ (In t [1; 2; 3])); [intros w [Ht _]; exact Ht|]. intros Ht.
      apply (TR_pre (SPA segs (JAv ndA1) (K_s t) rho' tp)); [intros w [_ Hw]; exact Hw|].
      apply (CUTV (K_s t) ndA1 1%nat (RL, VLA 10 z0) rho' tp); [| exact HPHI' | exact (HM (K_s t) ndA1 1%nat)].
      cbn [In] in Ht. destruct Ht as [<-|[<-|[<-|[]]]]; [right; left; reflexivity | do 2 right; left; reflexivity | do 3 right; left; reflexivity].
    + apply (CUTV K_sB ndA1 1%nat (RL, VLA 10 z0) rho' tp); [do 4 right; left; reflexivity | exact HPHI' | exact (HM K_sB ndA1 1%nat)].
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S10S8VKc;Vok;A3").
Variable FAMQ : list word -> assn.
Hypothesis XLATCH : ltac2:(tb__ "0|1|
S11S3S1dQ40A1A1M0G0S28S8Vok;S1aS8VJAFv;S39S2fA2S48R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Lemma PURE_nt_T : ltac2:(tb__ "0|0|
S2bVAInv;VCST;VXGL;VKc;VFB;VFF;VBX;Vrho0;S28S8Vok;A2S4aS49Ab").
Proof.
  intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
  apply (pure_callA segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HKc ALA ok Cl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_next_token.Pre_nt s R OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_next_token.Posts_nt rho1 tp1 nd Q'); try assumption.
  intros rho2 tp2. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_next_token.next_token_sum; [apply frozen_ok_frameA; exact Hok | apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
Qed.
Lemma PURE_si_T : ltac2:(tb__ "0|0|
S2bVAInv;VCST;VXGL;VKc;VFB;VFF;VBX;Vrho0;S28S8Vok;A2S4cS4bAb").
Proof.
  intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
  apply (pure_callA segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HKc ALA ok Cl Lib_scan_int.Pre_si s R Lib_scan_int.Posts_si rho1 tp1 nd Q'); try assumption.
  intros rho2 tp2. apply Lib_scan_int.scan_int_sum; [apply frozen_ok_frameA; exact Hok | apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
Qed.

Lemma CUTV_T : ltac2:(tb__ "0|5|
S18SbS2S1S9S12A2M0S11S3S1dQ40A1A1M1S9G1S3aS1S1S1S18SbA2M2S2A2M3G0A2S0G3G0S0G2S2S0S18SbR8R7A4R6A4R5A4S3cA3S32S47R7R5A3S22S1eZ0S31S0G3G0S0G2S2S0S18SbRaR9A4R8A4R7A4R6A2M4A2S1fG4R4A2A2S28S8Vok;S1aS8VJAv;RaA1RbR7R6A5VFAMQ;R4A1A4F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi _.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF_h segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads H_ecertS_ok 3000%nat cps_arm NP cutsS exitsS ok (FAMQ tp0') Hok
           ecertS_ok); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  cbn [exitsS In] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-; cbn [efdrop fst snd].
  -
    apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV 1)). intros HP1.
    pose proof as_checks2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CVB).
    apply (site_si (triple segs ok) (TRs_facts segs ok) (TRs_pre segs ok) PURE_si_T rho1 tp1); intros rho' HF Hag.
    + apply (reenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisV ok (map efdrop cutsS) T_s2n ndA1 1%nat (FAMQ tp0') rho' tp1); [do 5 right; left; reflexivity |].
      exact (phi_agree V_B tblB tblB_reads _ rho1 rho' CVB Hag HP1).
    + apply (reenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisV ok (map efdrop cutsS) T_s2y ndA1 1%nat (FAMQ tp0') rho' tp1); [do 6 right; left; reflexivity |].
      exact (phi_agree V_B tblB tblB_reads _ rho1 rho' CVB Hag HP1).
  - eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLATCH rho1 tp1 tp0')].
Qed.

Theorem arm_s_T : ltac2:(tb__ "0|1|
S11S3S1dQ40A1A1M0G0S28S8Vok;S1aS8VJAFv;S39S2cA2S38R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_s (triple segs ok) (fun _ tp0 => FAMQ tp0) (TRs_facts segs ok) (TRs_pre segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           (@triple_ex segs ok) (TRs_pureP segs ok) PURE_nt_T CUTV_T rho tp tp0).
Qed.
End Safety.

Section Existence.
Variable FAM : ltac2:(tb__ "0|0|
S9S3S1dQ40A1A1S26F_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
S9S9S3S1dQ40A1A1S29S1eR4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis XLATCH : ltac2:(tb__ "0|2|
S11S3S1dQ40A1A1M0G0S27S8S1aS8VJAFv;S39S2fA2S48R3R2A5VFAM;S31S0S1S1S18SbA2M1S2A2S1S9S12A2S0G1S2S0S18SbS48S2fA4U1A4S0S9S12S2dS2eZ1S30A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").

Lemma PURE_nt_E : ltac2:(tb__ "0|0|
S2bVAInv;VCST;VXGL;VKc;VFB;VFF;VBX;Vrho0;S27S8A1S4aS49Ab").
Proof.
  intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
  apply (pure_callA_ex segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HKc ALA Cl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_next_token.Pre_nt s R OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_next_token.Posts_nt rho1 tp1 nd Q'); try assumption.
  intros rho2 tp2. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_next_token.next_token_sum_ex. apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
Qed.
Lemma PURE_si_E : ltac2:(tb__ "0|0|
S2bVAInv;VCST;VXGL;VKc;VFB;VFF;VBX;Vrho0;S27S8A1S4cS4bAb").
Proof.
  intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
  apply (pure_callA_ex segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HKc ALA Cl Lib_scan_int.Pre_si s R Lib_scan_int.Posts_si rho1 tp1 nd Q'); try assumption.
  intros rho2 tp2. apply Lib_scan_int.scan_int_sum_ex. apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
Qed.

Lemma CUTV_E : ltac2:(tb__ "0|5|
S18SbS2S1S9S12A2M0S11S3S1dQ40A1A1M1S9G1S3aS1S1S1S18SbA2M2S2A2M3G0A2S0G3G0S0G2S2S0S18SbR8R7A4R6A4R5A4S3cA3S32S47R7R5A3S22S1eZ0S31S0G3G0S0G2S2S0S18SbRaR9A4R8A4R7A4R6A2M4A2S1fG4R4A2A2S27S8S1aS8VJAv;RaA1RbR7R6A5VFAM;R5R4A2A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi Hm.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) nd T rho tp _ Hphi).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (FAM_mono _ b tp0' w ltac:(apply Z.lt_le_incl; exact (proj2 Hm)) Hw) |].
  apply (cfg_complete_JAF_bh segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads H_ecertS_ok 3000%nat cps_arm NP cutsS exitsS (fun b w => FAM b tp0' w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0' w Hb Hw) ecertS_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX. cbn [exitsS In] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-.
  -
    apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV 1)). intros HP1.
    pose proof as_checks2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CVB).
    apply (site_si (etriple segs) (TRe_facts segs) (TRe_pre segs) PURE_si_E rho1 tp1); intros rho' HF Hag;
      (fact HF (SPUlt pI xLC) HiC; rewrite h_ult in HiC; fact HF (SPUle xLC vLEN) HcL; rewrite h_ule in HcL;
       fact HF (SPUle vLEN (SLit 67108864)) HL26; rewrite h_ule, uval_lit in HL26 by lia).
    + eapply (ereenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisV cutsS T_s2n ndA1 1%nat (RL, VLA 5 z0));
        [do 5 right; left; reflexivity | exact (phi_agree V_B tblB tblB_reads _ rho1 rho' CVB Hag HP1) |].
      apply (VLA_lt rho1 rho' 7 5 z0 E_si T_s2n ndA1 ndA1 1%nat 1%nat);
        [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
    + eapply (ereenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisV cutsS T_s2y ndA1 1%nat (RL, VLA 5 z0));
        [do 6 right; left; reflexivity | exact (phi_agree V_B tblB tblB_reads _ rho1 rho' CVB Hag HP1) |].
      apply (VLA_lt rho1 rho' 7 5 z0 E_si T_s2y ndA1 ndA1 1%nat 1%nat);
        [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
  - eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLATCH rho1 tp1 tp0')].
Qed.

Theorem arm_s_E : ltac2:(tb__ "0|2|
S11S3S1dQ40A1A1M0G0S27S8S1aS8VJAFv;S39S2cA2S38R3R2A5VFAM;S31S0S1S1S18SbA2M1S2A2S1S9S12A2S0G1S2S0S18SbS38S2cA4U1A4S0S9S12S2dS2eZ11S30A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_s (etriple segs) FAM (TRe_facts segs) (TRe_pre segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           (@etriple_ex segs) (TRe_pureP segs) PURE_nt_E CUTV_E rho tp tp0).
Qed.
End Existence.
End Sum.

