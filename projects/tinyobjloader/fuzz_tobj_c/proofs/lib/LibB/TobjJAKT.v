(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "prod"; "Some"; "pair"; "nil"; "option"; "cons"; "nat"; "fst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "rho_sub"; "wsub"; "in_ranges"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_next"; "ss_facts"; "sv"; "sprop"; "eval"; "holds"; "rw"; "sobj"; "SLit"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "cls_kept_freeA"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bitem"; "KU"; "bd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "nd_tv"; "ndesc"; "NDA"; "nd_am"; "nd_bd"; "nd_below"; "nd_fr"; "JA"; "JAi"; "JAk"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "call_checkPA"; "entails_frA"; "LQPA"; "J_ofPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "remove_nth"; "T0"; "tnz"; "tvv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "keptR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "call_checkTA"; "site_okA"; "payA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "V_TOP"; "ulink"; "unwind_stopJ"; "JL_free"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "HB"; "L_free_tol"; "PRES"; "Pre_free_tol"; "J_free_tol_pre"; "free_tol_contract"; "free_tol_contract_ex"; "@Stdlib.Lists.List"; "In"; "nth_error"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundI SymSoundM SymSoundR SymSoundW SymFrame SymEntail SymCFG SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAF.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Ltac cm_stack H := first [exact H | match goal with E : aa_geom _ = aa_geom _ |- _ => first [rewrite E; exact H | rewrite <- E; exact H] end].
Ltac top_rng H := match type of H with context [topG ?G] => let TG := fresh "TG" in pose proof (topG_range G) as TG end.

Section WithSegs.
Variable segs : list Segment.
Variable E : aentry.
Variable AInv : ltac2:(tb__ "0|0|
S2cS1eS6S2fQ40A1A1S50OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S5eVsegs;VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S5S69VCST;R1A2S1S15Z0R2A2S16R2S4fA2A2F_;Fa;").
Ltac hcst H := match type of H with _ /\ _ => let H' := fresh in destruct H as [H H']; apply HCST in H | _ => apply HCST in H end.
Hypothesis HXGL : ltac2:(tb__ "0|0|
S5S69VXGL;R1A2S1S15Z0R2A2S16R2S4fA2A2F_;Fa;").

Hypothesis HTOPI : InitState.segs_top segs <= IMG_HI.

Section Rt.
Variable NP : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S6S9S9S5S5A2S5A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Hypothesis HKc : Kc_ok Kc.

Context {dF : Z}.
Hypothesis HBX : BXok_d dF BX.

Let JAi : ltac2:(tb__ "0|0|
S36S2cS5S2aFkc;FAi;Fnd;") := ltac2:(tb__ "0|0|
S3dVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").
Let JA : ltac2:(tb__ "0|0|
S36S2aFnd;") := ltac2:(tb__ "0|0|
S3cVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").
Let JAk : ltac2:(tb__ "0|0|
S36S2cS2aFAi;Fnd;") := ltac2:(tb__ "0|0|
S3eVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").

Local Abbreviation AInv_absorb := (TobjJAM.AInv_absorb segs AInv CST ALA HCST).
Local Abbreviation KEPT_stepA := (TobjJAM.KEPT_stepA segs AInv CST XGL ALA).
Local Abbreviation T_of_chkA := (TobjJAM.T_of_chkA NP rho0).
Local Abbreviation call_checkTA := (TobjJAM.call_checkTA NP).
Local Abbreviation caller_X_kept := (TobjJAM.caller_X_kept segs AInv CST XGL ALA HCST HXGL).
Local Abbreviation client_not_shadow := (TobjJAM.client_not_shadow segs AInv CST ALA HCST).
Local Abbreviation cmaddrA := (TobjJAM.cmaddrA CST).
Local Abbreviation cont_JAi := (TobjJAM.cont_JAi segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0f FB FF BX PA).
Local Abbreviation cont_smatchA := (TobjJAM.cont_smatchA segs).
Let payA : ltac2:(tb__ "0|1|
S6S22A1S21S5S6S32A1M0G0OFbto;Fbfrom;FcostK;FcostV;Ffacts;") := ltac2:(tb__ "0|0|
S58VNP;Vrho0;VP0f;A3").
Local Abbreviation robjs_okA_weaken := (TobjJAM.robjs_okA_weaken CST).
Local Abbreviation shadow_not_in_R := (TobjJAM.shadow_not_in_R segs AInv CST ALA HCST).
Local Abbreviation site_okA := (TobjJAM.site_okA AInv CST XGL NP rho0 P0f FB FF).
Local Abbreviation top_of_TPA := (TobjJAM.top_of_TPA NP rho0).
Local Abbreviation tp_of_TPA := (TobjJAM.tp_of_TPA NP rho0).
Local Abbreviation xrs_range := (TobjJAM.xrs_range segs AInv CST XGL ALA HCST HXGL).
Local Abbreviation live2_kept := (TobjJAM.live2_kept segs AInv CST XGL ALA HCST).

Ltac chain_same_tv Hlink Hnb :=
  cbn zeta; intros ? ? _ _ Hut;
  eapply untracked_agree; [eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch] | | exact Hut];
  exact (proj1 (nd_below_split _ _ Hnb)).

Local Abbreviation keptR := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK.keptR).

Section CallTK.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S2aS3S1eS6S2fQ40A1A1S11S42S22S24R3A1S20S2R4A1A1A3VTR;S29Vsegs;R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S11S11S11S12R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S2aS2aS3S3S1cS6S26A1M0S6S9S3S45A2M1A1S6S9S21S21A2M2A1S11S1eS6S2fQ40A1A1M3G2S66G2R1R5A3S66G2R2S4RbA1A3F_;Fr;S0SdG0A1S47RaR9R8A3SaG0R7A2A3S0S7S46RbRaR9R8S43G1S3S10S3S45A2R7A4A5S8A3S1eG3VTR;S29Vsegs;RfRdR2R1A5S48Vsegs;S1fS2RdA1A1R2R1RaA5A2Ftp1;Frho1;S6S51A1M4S44S50S2bVsegs;R9R8R10SbG4S52R3S53R2R1A2A4A5R13RaR9R4R2A4R13S1bS1aRbRfS4aR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S3S45G4S44S50S1eG3G4S44S50S66G1SbS3S45RaR9A4R14A3S2bVsegs;R12R11R19SbG4S52R9S53R8R7A2A4A5R1cR13R12RaR8A4S40S1fS2R1aA1A1S1bS1aR14R18S4aR9R13RaA3A3R19A2R8A3S2bVsegs;R9R8ReSbG4S52R7S53R6R5A2A4A5ReS1bS1aR16R1aS4aRbR15RcA3A3R1bA2R15RaR9R8R6A6S1S6bR17S4aRcR16RdA3R1bR1cR1dR10R1eR19RbA9S1eS41R18S4aRdR17ReA3R1cR1dS2R1eA1S2R1fA1S2R11A1R1RcA9VTR;S29Vsegs;S49R11S1bS1aR19R1dS4aReR18RfA3A3R1eA2R18RdRcA5S6cR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S29Vsegs;R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Theorem free_tol_callT_k : ltac2:(tb__ "0|b|
S3S1cS6S26A1M0S1eS6S2fQ40M1A1A1M2S36SfS9S21S21A2M3S6S32A1S11S2cS1eG2VTR;S29Vsegs;S63Vsegs;VAInv;R3VKc;A4S62VE;A1M4R2R1A5S48Vsegs;S6aR2R1SeS9S3S45A2M5SbS3S45S60VE;A1M6S5dVAInv;VCST;VXGL;R3VKc;A5A4ScG5A1A3A5A2Ftp1;Frho1;FAi;S0SdG0A1S47RbG4RaA3SaG0R9A2A3S0S7S46RcG4RbRaSeS3G6ScS3A1A3A5S8A3S0S7S56VNP;RcA2S8A3S0S7S68VNP;S1fS2ReA1A1A2S8A3S0S7S3aS1fS2RfA1A1RaA2S8A3S0S7S34S1fS2R10A1A1R8A2S8A3S0SdG3A1S67G3S35RcA1RbA3SaG3RaA2A3VpayA;S20S2R12A1A1S27Z0A1S33S39RdA1RaA5S2cS2cVPA;R2A1S2dR3R2A2VPA;R3A1F_;F_;FA';FA;S57VAInv;VCST;VXGL;VNP;Vrho0;VP0f;VFB;VFF;R14R13R12R11RfSaS5S31R11S19R13PcM7A2A2A2S2cS44S1S4dR13RfA2S1S0S9S5S5A2S4eR13RfA2SbS5S5S31R13S19R15G7A2A2S31R13S19R15PdA2A2A4A3S5cScS5bA1S59S1bS1aR13R14R1A3R15A2A3A2A2Lms;LAi;AfVP0f;Vrho0;A1S61Vsegs;S28Vrho0;A1S2eG1S25Vrho0;PaM8A2A2M9S5fVrho0;A1A4F_;S42S22S24R13A1S20S2R16A1A1A3S40VNP;Vrho0;R14A3S1S15S4cVrho0;A1G9A2S1S15S17S2eG1S25Vrho0;S5aA2A2Z800000A2S18Z2Z2fA2A2S1S1S15S4fS2eG1S23R15S19R17G8A2A2A2MaA2S15GaG9A2A2S5S1S15S2eG1S23R16S19R18G8A2A2A2R1A2S16R1G9A2A2S1dR17R18S30G1R2A2A3F_;Fz;A2A2A2F_;F_;S1eG2S40S1fS2R19A1A1R16R2A3S54R17S4bG3R14S35R15A1A3R3A3VTR;S29Vsegs;VJA;S37S4bG3R15S35R16A1A3S3bR16A1R13S38R16A1A4A1S55G4R1bR1aR19G6A5R4R3A5R12A2F_;F_;Ftp';Frho';VTR;S29Vsegs;VJA;R13A1R18R15R14A5RfA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Ft;Fi;Fnd;Ftp;Frho;FR;Fs;FCl;").
Proof using ALA HCST HXGL HTOPI HKc TR_callP TR_ex TR_facts TR_pre.
  intros Cl s R rho tp nd i t bd' Q CALLEE He Hchk Htp Hnf Hnb Hbb Hnth HPAY HPAK HSITE HPZ HCOV Tfree.
  apply Pos.leb_le in Hnf.
  apply TR_facts. intros HF.
  apply (TR_ex AA (JAk nd)). intros Ai. apply (TR_ex Z (JAi nd Ai)). intros kc.
  set (p := uval rho (wsub_get s 12)) in *. set (n := uval rho (wsub_get s 13)) in *.
  eapply (TR_callP (JAi nd Ai kc) (J_free_tol_pre segs AInv Ai Kc) Cl (Pre_free_tol E) s R
            [(L_free_tol E, JL_free AInv CST XGL Ai Kc)] (ax_X Cl) Q rho tp (fun r H => H) He).
  - exact Hchk.
  - intros rho1 tp1. apply CALLEE.
  -
    intros tr ms md Hsm HJ. pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    destruct (HSITE Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA Ai s rho Hav HT Htp)) as (HRok & HX & Hnz & Ht & HU).
    split; [|split].
    2:{
        pose proof HBU as (_ & B2 & _ & _ & _ & Bw & Bn & _ & B9). pose proof (bsum_nonneg _ rho Bw Bn) as [_ B8]. unfold KU in B9. lia. }
    2:{
        destruct (HCOV HF Hav) as (C1 & C2 & C3 & C4).
        assert (EHB : OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol.HB (rho_sub (rho_absorb rho R (vms md tp ms)) s) = OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol.HB rho0).
        { unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol.HB. f_equal. pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.T0_calleeA NP rho0 s rho R (vms md tp ms) Hav Htp) as X0. unfold T0 in X0. exact X0. }
        rewrite rw_call', EHB. pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAP.HBz_le_47 _ C2) as HB47. fold (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol.HB rho0) in HB47.
        apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAP.PRES_callee segs rho R (vms md tp ms) s); [exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJACP.R_present segs HTOPI Cl (Pre_free_tol E) s R rho tp tr ms md He Hsm) | lia | lia |].
        intros z Hz. destruct (Z_lt_le_dec z (bv_unsigned (rw rho0 10%positive))) as [Hlo|Hhi]; [left; apply C4; lia | right].
        unfold IMG_HI in C3.
        exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAP.PRES_keptFA segs CST XGL rho0 FB FF (rm rho0) (rm rho) (bv_unsigned (rw rho0 10%positive)) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol.HB rho0) HK0 C1 ltac:(lia) HB47 (HPZ HP0) z ltac:(lia)). }
    split; [eapply AInv_absorb; [exact HM | eapply robjs_okA_weaken; exact HRok]|]. split; [exact HU|].
    split.
    { rewrite !rw_call'. destruct (proj1 (Forall_forall _ _) HN t (nth_error_In _ _ Hnth) Hnz) as (_ & X1 & _). rewrite Ht in X1. exact X1. }
    split; [exact Hk|]. split; [eapply tp_of_TPA; eauto|].
    pose proof HBU as (_ & _ & _ & _ & _ & HwF & HnF & _).
    destruct HPAY as (HwT & HcK & HPS). destruct (HPS rho HF (conj HP0 Hav) HwF HnF) as (P1 & P2 & NNT). pose proof (bsum_nonneg bd' rho HwT NNT) as [P3 P4].
    split; [|exact (top_of_TPA Ai s rho _ _ Hav HT Htp)].
    eapply (BUD_limit_ok_free (nd_bd nd) _); [exact HBU | lia].
  -
    intros L JL tr ms md rhoL tpL tr' ms' md' HinL Hsm HJ Hag1 HsmL HJL.
    pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    destruct (HSITE Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA Ai s rho Hav HT Htp)) as (HRok & HX & Hnz & Ht & HU).
    pose proof (entails_frA_base _ _ _ _ SHADOW_OFF He eq_refl) as HbC.
    destruct HinL as [HinL | []]; injection HinL as HL HJLe; subst L JL.
    destruct HJL as (A2 & l1 & l2 & HM2 & HLi & HL2 & HF2 & HV2 & HKm2 & HKf2 & HG2 & Hkept2 & Hk2 & HC2).
    rewrite !rw_call' in HLi. fold p n in HLi. change (bv_unsigned (eval rho (wsub_get s 12))) with p in HLi. change (bv_unsigned (eval rho (wsub_get s 13))) with n in HLi.
    destruct (proj1 (Forall_forall _ _) HN t (nth_error_In _ _ Hnth) Hnz) as (Tpos & Tin & TFB). rewrite Ht in Tpos, Tin, TFB. cbn [snd] in Tpos.
    destruct (law_blocks _ _ _ ALA Ai _ _ _ HM) as (HPD & HBl & HFr).
    assert (SAMEBASE : forall b m, In (b, m) (aa_live Ai) -> b <> p -> In (b, m) (l1 ++ l2)).
    { intros b m Hin Hne. rewrite HLi in Hin. destruct (in_mid_cases' l1 l2 (p, n) (b, m) Hin) as [E0|Hin']; [|exact Hin'].
      exfalso. injection E0. lia. }
    assert (Hsub : forall a, cmaddrA Ai (Some p) a -> cmaddrA A2 None a).
    { intros a [H|[H|[(b & m & Hin & Hx & Hr)|(f & sz & Hin & Hr)]]]; [left; cm_stack H | right; left; exact H | |].
      - right; right; left. exists b, m. rewrite HL2. split; [apply SAMEBASE; [exact Hin | intros ->; apply Hx; reflexivity] | auto].
      - right; right; right. exists f, sz. rewrite HF2. auto. }
    assert (HFB2 : forall b, In b FB -> In b (aa_live A2)).
    { intros [b m] Hb. rewrite HL2. pose proof (HB _ Hb) as Hin. rewrite HLi in Hin.
      destruct (in_mid_cases' l1 l2 (p, n) (b, m) Hin) as [E0|Hin']; [|exact Hin']. exfalso. apply TFB. rewrite <- E0. exact Hb. }
    split.
    * split; [split; [exact (KEPT_stepA Ai A2 (Some p) rho rhoL _ s R _ _ _ HM HRok Hsub Hkept2)|]|split].
      -- intros o' oR Hin' _. exfalso. destruct (new_objs_not_pre _ _ _ Hin') as [A B0].
         cbn [ax_S L_free_tol Pre_free_tol mkA ss_objs] in A, B0. apply B0.
         apply in_inv in A as [A|A]; [left; exact A|]. right. apply in_or_app. right. exact A.
      -- intros r a j oR Hr. cbn in Hr. destruct Hr.
      -- eapply (caller_X_kept Ai A2 (Some p) rho tp md R (vms md tp ms) s rhoL Cl); eauto.
         all: first [ solve [eapply xrs_range; eauto]
                    | (intros o' Hin'; exfalso; destruct (new_objs_not_pre _ _ _ Hin') as [A B0];
                       cbn [ax_S L_free_tol Pre_free_tol mkA ss_objs] in A, B0; apply B0;
                       apply in_inv in A as [A|A]; [left; exact A|]; right; apply in_or_app; right; exact A) ].
    * intros rho' Hlink.
      assert (HagP0 : agree_vals (ss_next (ax_S Cl)) rho (rho_patch rho' (patchf rho rho' R))) by (eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch]).
      assert (KR : keptR rho (remove_nth i (nd_tv nd)) (rho_patch rho' (patchf rho rho' R))).
      { intros t0 z Ht0 Hnz0 Hz. destruct (proj1 (Forall_forall _ _) HN t0 (remove_nth_In _ _ _ Ht0) Hnz0) as (_ & Hl0 & _).
        refine (proj1 (live2_kept Ai A2 (Some p) rho rho' rhoL (vms md tp ms) s R tp md _ _ HM HRok Hkept2 (proj1 (proj2 Hlink)) Hl0 _) z Hz).
        rewrite HL2. pose proof Hl0 as Hl1. rewrite HLi in Hl1. destruct (in_mid_cases' l1 l2 (p, n) (tvv rho t0) Hl1) as [E0|Hin']; [|exact Hin'].
        exfalso. apply (tvd_nth_distinct rho (nd_tv nd) i t t0 HD Hnth Ht0 Hnz Hnz0). rewrite Ht. exact E0. }
      eapply TR_pre; [ | apply (Tfree (rho_patch rho' (patchf rho rho' R)) tpL HagP0 KR)].
      intros w [Hsm' HJ']. cbn [J_ofPA] in HJ'.
      destruct HJ' as (A3 & k1 & k2 & HM3 & HLi3 & HL3 & HF3 & HV3 & HKm3 & HKf3 & HG3 & Hkept3 & Hk3 & HC3).
      rewrite !rw_call' in HLi3. change (bv_unsigned (eval rho (wsub_get s 12))) with p in HLi3. change (bv_unsigned (eval rho (wsub_get s 13))) with n in HLi3.
      destruct w as [trw [msw mdw]]. cbn [w_tr w_cfg fst snd cfg_model] in *.
      split; [exact (cont_smatchA Cl (Pre_free_tol E) _ s R rho rho' tp tpL tr ms md _ He Hsm (proj1 Hlink) Hsm')|].
      exists A3, kc.
      assert (SAMEBASE3 : forall b m, In (b, m) (aa_live Ai) -> b <> p -> In (b, m) (k1 ++ k2)).
      { intros b m Hin Hne. rewrite HLi3 in Hin. destruct (in_mid_cases' k1 k2 (p, n) (b, m) Hin) as [E0|Hin']; [|exact Hin'].
        exfalso. injection E0. lia. }
      assert (DIST3 : forall bm, In bm (aa_live Ai) -> bm <> (p, n) -> In bm (k1 ++ k2)).
      { intros bm Hin Hne. rewrite HLi3 in Hin. destruct (in_mid_cases' k1 k2 (p, n) bm Hin) as [E0|Hin']; [exfalso; exact (Hne E0)|exact Hin']. }
      assert (Hsub' : forall a, cmaddrA Ai (Some p) a -> cmaddrA A3 None a).
      { intros a [H|[H|[(b & m & Hin & Hx & Hr)|(f & sz & Hin & Hr)]]]; [left; cm_stack H | right; left; exact H | |].
        - right; right; left. exists b, m. rewrite HL3. split; [apply SAMEBASE3; [exact Hin | intros ->; apply Hx; reflexivity] | auto].
        - right; right; right. exists f, sz. rewrite HF3. auto. }
      destruct (law_budget _ _ _ ALA A3 _ _ _ HM3) as (_ & _ & HV0 & HKm0 & HKf0).
      assert (HagP : agree_vals (ss_next (ax_S Cl)) rho (rho_patch rho' (patchf rho rho' R))).
      { eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch]. }
      pose proof Hnb as Hnb0. destruct (nd_below_split _ _ Hnb) as (Hbt & _ & _ & _).
      assert (Hbt' : tv_below (ss_next (ax_S Cl)) (remove_nth i (nd_tv nd)) = true).
      { unfold tv_below in *. apply forallb_forall. intros t' Ht'. apply (proj1 (forallb_forall _ _) Hbt). eapply remove_nth_In. exact Ht'. }
      pose proof (HPAK Ai A3 HPA HC3) as HPA2.
      eapply (cont_JAi Cl (Pre_free_tol E) (L_free_tol E) s R rho tp tr ms md rhoL tpL trw mdw rho' nd Ai kc A3 (Some p)
                _ bd' (SLit 0) KU He Hsm Hnf Hnb0 Hbb HJ HRok Hlink HM3 Hk3 Hsub'); try assumption.
      -- intros [b m] Hb. rewrite HL3. apply DIST3; [exact (HB _ Hb)|]. intros E0. apply TFB. rewrite <- E0. exact Hb.
      -- rewrite HV3. pose proof (uval_range rho (SLit 0)). lia.
      -- rewrite HKm3, HKf3. unfold KU. lia.
      -- cbn zeta. split; [|split].
         ++ apply (tvinA_agree FB A3 (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt' |].
            unfold tvinA in HN |- *. apply Forall_forall. intros t' Ht' Hnz'.
            destruct (proj1 (Forall_forall _ _) HN t' (remove_nth_In _ _ _ Ht') Hnz') as (X0 & X1 & X2).
            split; [exact X0|]. split; [|exact X2]. rewrite HL3. apply DIST3; [exact X1|].
            rewrite <- Ht. exact (tvd_nth_distinct rho (nd_tv nd) i t t' HD Hnth Ht' Hnz Hnz').
         ++ apply (tvd_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt' | apply tvd_remove; exact HD].
         ++ apply (tvz_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt' |].
            unfold tvz in HZ |- *. apply Forall_forall. intros t' Ht'. apply (proj1 (Forall_forall _ _) HZ). eapply remove_nth_In. exact Ht'.
      --
         intros b m Hb _ Hut. rewrite HL3. apply DIST3; [exact Hb|]. intros E0.
         apply (proj1 (untracked_tv _ _ _) Hut t (nth_error_In _ _ Hnth) Hnz). rewrite Ht. symmetry. exact E0.
      -- cbn zeta. intros b m _ _ Hut. eapply untracked_agree; [exact HagP | exact Hbt' |].
         eapply untracked_sub; [| exact Hut]. intros t' Ht'. eapply remove_nth_In. exact Ht'.
      -- cbn zeta. destruct (HBl p n ltac:(rewrite HLi3; apply in_or_app; right; left; reflexivity)) as (Gn & _).
         exact (TobjJAM.cen_remove FB Ai A3 rho _ _ (nd_tv nd) i t k1 k2 p n (aa_frames Ai) HagP Hbt Hnth Ht Gn HLi3 HL3 ltac:(rewrite <- HLi3; exact HPD)).
      -- apply (TobjJAM.capK_remove BX Ai A3 k1 k2 p n HCKi HLi3 HL3). rewrite HV3. lia.
      -- exact (TobjJAM.capN_remove BX Ai A3 _ rho _ (nd_tv nd) i t k1 k2 p n HCNi HLi3 HL3 HagP Hbt Hnth Ht Hnz).
Qed.

End CallTK.

Let TRs (ok : world -> Prop) : assn -> assn -> Prop := triple segs ok.
Let TRe : assn -> assn -> Prop := etriple segs.
Lemma TRs_facts : ltac2:(tb__ "0|1|
S12OF_;S2aS3S1eS6S2fQ40A1A1S11S42S22S24R3A1S20S2R4A1A1A3VTRs;R7S29Vsegs;R6R5R4R3A5R2A3M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;Fok;").
Proof using . intros ok. exact (triple_factsA segs ok). Qed.
Lemma TRs_ex : forall ok (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TRs ok (SPA segs (J x) S rho tp) Q) -> TRs ok (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Proof using . intros ok. exact (triple_SPA_ex segs ok). Qed.
Lemma TRs_pre : ltac2:(tb__ "0|0|
S12OF_;S11S11S11S12R3R1A1R5R2A1F_;Fw;VTRs;R5R4R2A3VTRs;R6R4R3A3F_;F_;FQ;FP';FP;Fok;").
Proof using segs. intros ok P P' Q HP H. eapply triple_conseq; [exact HP | intros w Hw; exact Hw | exact H]. Qed.
Lemma TRe_facts : ltac2:(tb__ "0|1|
S2aS3S1eS6S2fQ40A1A1S11S42S22S24R3A1S20S2R4A1A1A3VTRe;S29Vsegs;R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Proof using . exact (etriple_factsA segs). Qed.
Lemma TRe_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TRe (SPA segs (J x) S rho tp) Q) -> TRe (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Proof using . exact (etriple_SPA_ex segs). Qed.
Lemma TRe_pre : ltac2:(tb__ "0|0|
S11S11S11S12R3R1A1R5R2A1F_;Fw;VTRe;R4R2A2VTRe;R4R3A2F_;F_;FQ;FP';FP;").
Proof using segs. intros P P' Q HP H. eapply etriple_conseq; [exact HP | intros w Hw; exact Hw | exact H]. Qed.

Lemma TRe_pureP : ltac2:(tb__ "0|1|
S11OS11S12R4R1A1R4F_;Fw;R3VTRe;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Proof using . clear. intros P X Q HX H w Hw. exact (H (HX w Hw) w Hw). Qed.
Lemma TRs_pureP : ltac2:(tb__ "0|1|
S12OF_;S11OS11S12R4R1A1R4F_;Fw;R3VTRs;R6R5R3A3M0F_;G0F_;F_;FQ;FX;FP;Fok;").
Proof using . clear. intros ok P X Q HX H n Hg w Hw. exact (H (HX w Hw) n Hg w Hw). Qed.

Ltac by_callT_safety ok lem :=
  apply (lem (triple segs ok) (TRs_facts ok) (TRs_ex ok) (TRs_pre ok) (call_soundPA3 segs ok)).
Ltac by_callT_ex lem :=
  apply (lem (etriple segs) TRe_facts TRe_ex TRe_pre (call_completePA3 segs)).

Theorem free_tol_callA_k : ltac2:(tb__ "0|a|
S12OF_;S3S1cS6S26A1M0S1eS6S2fQ40M1A1A1M2S36SfS9S21S21A2M3S6S32A1S11S3fVsegs;VKc;RbA3S64Vsegs;VE;VAInv;VCST;VXGL;A5S0SdG0A1S47RcS62VE;A1M4RbA3SaG0RaA2A3S0S7S46RdG4RcRbSeS3S60VE;A1M5ScS3A1A3A5S8A3S0S7S56VNP;RdA2S8A3S0S7S68VNP;S1fS2RfA1A1A2S8A3S0S7S3aS1fS2R10A1A1RbA2S8A3S0S7S34S1fS2R11A1A1R9A2S8A3S0SdG3A1S67G3S35RdA1RcA3SaG3RbA2A3VpayA;S20S2R13A1A1S27Z0A1S33S39ReA1RbA5S2cS2cVPA;R2A1S2dR3R2A2VPA;R3A1F_;F_;FA';FA;S57VAInv;VCST;VXGL;VNP;Vrho0;VP0f;VFB;VFF;R15R14R13R12R10SaS5S31R12S19R14PcM6A2A2A2S2cS44S1S4dR14R10A2S1S0S9S5S5A2S4eR14R10A2SbS5S5S31R14S19R16G6A2A2S31R14S19R16PdA2A2A4A3S5cScS5bA1S59S1bS1aR14R15R1A3R16A2A3A2A2Lms;LAi;AfVP0f;Vrho0;A1S61Vsegs;S28Vrho0;A1S2eG1S25Vrho0;PaM7A2A2M8S5fVrho0;A1A4F_;S42S22S24R14A1S20S2R17A1A1A3S40VNP;Vrho0;R15A3S1S15S4cVrho0;A1G8A2S1S15S17S2eG1S25Vrho0;S5aA2A2Z800000A2S18Z2Z2fA2A2S1S1S15S4fS2eG1S23R16S19R18G7A2A2A2M9A2S15G9G8A2A2S5S1S15S2eG1S23R17S19R19G7A2A2A2R1A2S16R1G8A2A2S1dR18R19S30G1R2A2A3F_;Fz;A2A2A2F_;F_;S1eG2S40S1fS2R1aA1A1R17R2A3S54R18S4bG3R15S35R16A1A3R3A3S14Vsegs;R1dS29Vsegs;VJA;S37S4bG3R16S35R17A1A3S3bR17A1R14S38R17A1A4A1S55G4R1cR1bR1aG5A5R4R3A5R13A4F_;F_;Ftp';Frho';S14Vsegs;R1aS29Vsegs;VJA;R14A1R19R16R15A5R10A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Ft;Fi;Fnd;Ftp;Frho;FR;Fs;FCl;Fok;").
Proof using ALA HCST HXGL HTOPI HKc.
  intros ok Cl s R rho tp nd i t bd' Q Hok AC. by_callT_safety ok free_tol_callT_k.
  intros Ai rho1 tp1. exact (AC ok Ai Kc rho1 tp1 HKc (proj1 Hok) (proj2 Hok)).
Qed.

Theorem free_tol_callA_ex_k : ltac2:(tb__ "0|a|
S3S1cS6S26A1M0S1eS6S2fQ40M1A1A1M2S36SfS9S21S21A2M3S6S32A1S11S65Vsegs;VE;VAInv;VCST;VXGL;A5S0SdG0A1S47RbS62VE;A1M4RaA3SaG0R9A2A3S0S7S46RcG4RbRaSeS3S60VE;A1M5ScS3A1A3A5S8A3S0S7S56VNP;RcA2S8A3S0S7S68VNP;S1fS2ReA1A1A2S8A3S0S7S3aS1fS2RfA1A1RaA2S8A3S0S7S34S1fS2R10A1A1R8A2S8A3S0SdG3A1S67G3S35RcA1RbA3SaG3RaA2A3VpayA;S20S2R12A1A1S27Z0A1S33S39RdA1RaA5S2cS2cVPA;R2A1S2dR3R2A2VPA;R3A1F_;F_;FA';FA;S57VAInv;VCST;VXGL;VNP;Vrho0;VP0f;VFB;VFF;R14R13R12R11RfSaS5S31R11S19R13PcM6A2A2A2S2cS44S1S4dR13RfA2S1S0S9S5S5A2S4eR13RfA2SbS5S5S31R13S19R15G6A2A2S31R13S19R15PdA2A2A4A3S5cScS5bA1S59S1bS1aR13R14R1A3R15A2A3A2A2Lms;LAi;AfVP0f;Vrho0;A1S61Vsegs;S28Vrho0;A1S2eG1S25Vrho0;PaM7A2A2M8S5fVrho0;A1A4F_;S42S22S24R13A1S20S2R16A1A1A3S40VNP;Vrho0;R14A3S1S15S4cVrho0;A1G8A2S1S15S17S2eG1S25Vrho0;S5aA2A2Z800000A2S18Z2Z2fA2A2S1S1S15S4fS2eG1S23R15S19R17G7A2A2A2M9A2S15G9G8A2A2S5S1S15S2eG1S23R16S19R18G7A2A2A2R1A2S16R1G8A2A2S1dR17R18S30G1R2A2A3F_;Fz;A2A2A2F_;F_;S1eG2S40S1fS2R19A1A1R16R2A3S54R17S4bG3R14S35R15A1A3R3A3S13Vsegs;S29Vsegs;VJA;S37S4bG3R15S35R16A1A3S3bR16A1R13S38R16A1A4A1S55G4R1bR1aR19G5A5R4R3A5R12A3F_;F_;Ftp';Frho';S13Vsegs;S29Vsegs;VJA;R13A1R18R15R14A5RfA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Ft;Fi;Fnd;Ftp;Frho;FR;Fs;FCl;").
Proof using ALA HCST HXGL HTOPI HKc.
  intros Cl s R rho tp nd i t bd' Q ACX. by_callT_ex free_tol_callT_k.
  intros Ai rho1 tp1. exact (ACX Ai Kc rho1 tp1 HKc).
Qed.
End Rt.
End WithSegs.
