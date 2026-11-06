(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require IfaceS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.

(* [comment removed for export] *)
Module DrvSiteS.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "cons"; "prod"; "length"; "nil"; "None"; "Some"; "option"; "pair"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub"; "rho_absorb"; "rho_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "of_nat"; "lt"; "pow"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "valuation"; "SVar"; "sobj"; "ss_facts"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "PRIM_LIVE_MAX"; "SEC_SLACK"; "aa_Kf"; "aa_Km"; "aa_V"; "cls_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "Pre_malloc"; "L_malloc_ok"; "V_RES"; "malloc_shape"; "ulink"; "unwind_stopJ"; "ustop"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "KU"; "BUD"; "bitem"; "bd_below"; "bx2"; "bxN"; "bsumK"; "bsumV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "nd_am"; "nd_tv"; "nd_bd"; "JA"; "ndesc"; "ANone"; "NDA"; "amode"; "apot"; "bxa"; "nd_below"; "nd_fr"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "pos_add_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "import_subA"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "call_checkTA"; "payA"; "site_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.IfaceS"; "alloc_roomA"; "malloc_contractA_strong"; "malloc_contractA_strong_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "KMAX"; "VMAX"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymSummary SymEntail SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA SummaryA GlueA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface IfaceEx IfaceS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAM.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma call_checkPA_drop1 : ltac2:(tb__ "0|1|
S15S15S11S5S20A1S15S15S1S3S4bR6R5R4R3S6S15R2S6S15R1S9S15A1M0A3A3A5S4A3S1S3S4bR7R6R5R4S6S15R2G0A3A5S4A3F_;FP2;FP1;FR;Fs;FPre;FC;").
Proof.
  intros C Pre s R P1 P2 H. unfold call_checkPA, call_checkP in *. cbn [map forallb] in *.
  rewrite !Bool.andb_true_iff in H. rewrite !Bool.andb_true_iff. tauto.
Qed.

Lemma BUD_room : ltac2:(tb__ "0|3|
S5S35A1S7S0S0A2S0S0S0S1eS34R6R5R4R3R2R1A6S2S16Z0M0SeS0S0R6A3M1A2S2S16G0SfS0S0R6A3M2A2S2S16S17S17R5S3aR7R2A2A2G1A2S60A2S16S17S17S1bS33S17R4R3A2A2S39R7R2A2A2G2A2S1bS33S5fA2A2A2A2A2F_;Frho;FKf;FKm;FV;FP2;Fb;").
Proof. intros b P2 V Km Kf rho (A1 & A2 & _ & _ & _ & _ & _ & B1 & B2). repeat split; assumption. Qed.

Section WithSegs.
Variable segs : list Segment.
Variable E : aentry.
Variable AInv : ltac2:(tb__ "0|0|
S23S1eS5S4eQ40A1A1S5eOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S31Vsegs;VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S0S5cVCST;R1A2S2S16Z0R2A2S19R2S58A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S0S5cVXGL;R1A2S2S16Z0R2A2S19R2S58A2A2F_;Fa;").
Section Sum.
Variable NP : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S5S7S7S0S0A2S0A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Hypothesis HKc : Kc_ok Kc.
Let JA : ltac2:(tb__ "0|0|
S3fS4aFnd;") := ltac2:(tb__ "0|0|
S3eVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").

Theorem malloc_callA_S : ltac2:(tb__ "0|8|
S23OF_;S53OF_;S5S2eA1S30S15S11S5S20A1M0S1eS5S4eQ40A1A1M1S3fS5S35A1S50S2dRaR9A2S47Vsegs;VKc;RcA3S5aVsegs;VE;VAInv;VCST;VXGL;A5S1ScG0A1S4cRbS2aVE;RdRcA3RaA3SbG0R9A2A3S1S3S4bRcS2aVE;ReRdA3RbRaS6S15S2bVE;ReRdA3S9S15A1A3A5S4A3S1S3S55VNP;RcA2S4A3S1S3S5dVNP;S1cS14ReA1A1A2S4A3S1S3S45S1cS14RfA1A1RaA2S4A3S1S3S36S1cS14R10A1A1RaA2S4A3S1S3S22S1cS14R11A1A1S10R10PcM2A2A2S4A3S1S1dS10S4dR11S2aVE;R14R13A3S2bVE;R14R13A3R12A4S2cA2S1fS48S1cS14R12A1A1UaM3A2A1A3S56VNP;Vrho0;VP0f;S21S14R13A1A1S10R12G2A2S33S3dReA1RdA8S23S23VPA;R2A1M4S29R3R2S32R14S10R16G2A2A2A3R1cR3A1F_;F_;FA';FA;S23S0G4S16Z0R2A2S34S3dR14A1S44S37VBX;A1S43S3bR14A1R16A2R3A3S28R4A1S27R4A1S26R4A1R16A6S59R5S32R17S10R19G2A2A2A2F_;F_;F_;Fkc;FA;S1S42S3bR11A1S40A3S16S17S17S18S8S7S0S0A2VFB;A2A1S18S8S7S1dS1dA2M5S3cR12A1A2A1A2S25A2S1aZ2M6Z14A2A2S16S17S38VBX;A1S18S8G5S3cR13A1A2A1A2S24A2S57VAInv;VCST;VXGL;VNP;Vrho0;VP0f;VFB;VFF;R19R18R17R16R14SaS0A1S23S4fS2S2S16Z1S32R18S10R1aG2A2A2M7A2S19G7S1aG6Z27A2A2A2S2fR1dR1cS13S12R18R19R1A3R1aA2A3A2Lms;LAi;AfS1eG1S52Vsegs;R1fS49Vsegs;S3eVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;R20S41S6G5SdS1dS1dS1fS48S1cS14R1cA1A1G3A2A1S10R1bG2A2A4S3cR17A1A3S46R17A1R16S3bR17A1A4AcS54S2aVE;R1eR1dA3R1cR1bR1aS2bVE;R1eR1dA3A5R2R1A5R15A4Ftp';Frho';S52Vsegs;R1eS49Vsegs;VJA;R16A1R1bR18R17A5R14A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Fnd;Ftp;Frho;FR;Fs;FCl;Fst;FW;Fok;FPA';").
Proof using ALA HCST HXGL HKc.
  intros PA' ok W st Cl s R rho tp nd bd' Q HW Hok MS He Hchk Htp Hnf Hnb Hbb Hs12 Hres HPAY HPAK HROOM Ham Hfew Hprim HSITE Tok.
  apply (malloc_callT_gen_sec segs E AInv CST XGL ALA HCST HXGL NP Kc rho0 P0f FB FF BX PA HKc (triple segs ok) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok)
           (call_soundPA3 segs ok) false true (fun A r => alloc_roomA A (bv_unsigned (rw r 12%positive))) PA' W st Cl s R rho tp nd bd' Q); try assumption.
  - intros Ai rho1 tp1.
    apply (TRs_pureP segs ok _ (alloc_roomA Ai (bv_unsigned (rw rho1 12%positive)))); [intros w [_ [_ H]]; exact H|]. intros Hroom.
    apply (TRs_pre segs ok (SPA segs (J_alloc_pre AInv W st Ai Kc (SVar 12)) (Pre_malloc E W st) rho1 tp1)); [intros w [Hsm [HJ _]]; exact (conj Hsm HJ)|].
    apply (MS W st ok Ai Kc rho1 tp1 HW HKc (proj1 Hok) (proj2 Hok)). intros tr md _. exact Hroom.
  - intros A ms kc HP Hkc HB. cbn beta. rewrite rw_call'. exact (HROOM A kc HP Hkc HB).
  -   intros Ai kc tr md HJ. destruct nd as [tv fr bd am]. cbn [nd_am nd_tv] in Ham, Hfew. subst am.
    pose proof (JAi_large_live_le0 segs AInv CST XGL ALA NP Kc rho0 P0f FB FF BX PA tv fr bd Ai kc rho tp tr md HJ) as LL. unfold sec_room. lia.
  -   intros Ai kc tr md HJ.
    pose proof (JAi_small_live_le AInv CST XGL NP Kc rho0 P0f FB FF BX PA nd Ai kc rho tp tr md HJ) as SL. unfold prim_room. lia.
  - intros E0. discriminate E0.
  - intros _. exact Tok.
Qed.

Theorem malloc_callA_ex_S : ltac2:(tb__ "0|8|
S23OF_;S5S2eA1S30S15S11S5S20A1M0S1eS5S4eQ40A1A1M1S3fS5S35A1S50S2dRaR9A2S5bVsegs;VE;VAInv;VCST;VXGL;A5S1ScG0A1S4cRaS2aVE;RcRbA3R9A3SbG0R8A2A3S1S3S4bRbS2aVE;RdRcA3RaR9S6S15S2bVE;RdRcA3S9S15A1A3A5S4A3S1S3S55VNP;RbA2S4A3S1S3S5dVNP;S1cS14RdA1A1A2S4A3S1S3S45S1cS14ReA1A1R9A2S4A3S1S3S36S1cS14RfA1A1R9A2S4A3S1S3S22S1cS14R10A1A1S10RfPcM2A2A2S4A3S1S1dS10S4dR10S2aVE;R13R12A3S2bVE;R13R12A3R11A4S2cA2S1fS48S1cS14R11A1A1UaM3A2A1A3S56VNP;Vrho0;VP0f;S21S14R12A1A1S10R11G2A2S33S3dRdA1RcA8S23S23VPA;R2A1M4S29R3R2S32R13S10R15G2A2A2A3R1aR3A1F_;F_;FA';FA;S23S0G4S16Z0R2A2S34S3dR13A1S44S37VBX;A1S43S3bR13A1R15A2R3A3S28R4A1S27R4A1S26R4A1R15A6S59R5S32R16S10R18G2A2A2A2F_;F_;F_;Fkc;FA;S1S42S3bR10A1S40A3S16S17S17S18S8S7S0S0A2VFB;A2A1S18S8S7S1dS1dA2M5S3cR11A1A2A1A2S25A2S1aZ2M6Z14A2A2S16S17S38VBX;A1S18S8G5S3cR12A1A2A1A2S24A2S57VAInv;VCST;VXGL;VNP;Vrho0;VP0f;VFB;VFF;R18R17R16R15R13SaS0A1S23S4fS2S2S16Z1S32R17S10R19G2A2A2M7A2S19G7S1aG6Z27A2A2A2S2fR1cR1bS13S12R17R18R1A3R19A2A3A2Lms;LAi;AfS1eG1S51Vsegs;S49Vsegs;S3eVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;R1eS41S6G5SdS1dS1dS1fS48S1cS14R1bA1A1G3A2A1S10R1aG2A2A4S3cR16A1A3S46R16A1R15S3bR16A1A4AcS54S2aVE;R1dR1cA3R1bR1aR19S2bVE;R1dR1cA3A5R2R1A5R14A3Ftp';Frho';S51Vsegs;S49Vsegs;VJA;R15A1R1aR17R16A5R13A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Fnd;Ftp;Frho;FR;Fs;FCl;Fst;FW;FPA';").
Proof using ALA HCST HXGL HKc.
  intros PA' W st Cl s R rho tp nd bd' Q HW MSX He Hchk Htp Hnf Hnb Hbb Hs12 Hres HPAY HPAK HROOM Ham Hfew Hprim HSITE Tok.
  apply (malloc_callT_gen_sec segs E AInv CST XGL ALA HCST HXGL NP Kc rho0 P0f FB FF BX PA HKc (etriple segs) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs)
           (call_completePA3 segs) false true (fun A r => alloc_roomA A (bv_unsigned (rw r 12%positive))) PA' W st Cl s R rho tp nd bd' Q); try assumption.
  - intros Ai rho1 tp1.
    apply (TRe_pureP segs _ (alloc_roomA Ai (bv_unsigned (rw rho1 12%positive)))); [intros w [_ [_ H]]; exact H|]. intros Hroom.
    apply (TRe_pre segs (SPA segs (J_alloc_pre AInv W st Ai Kc (SVar 12)) (Pre_malloc E W st) rho1 tp1)); [intros w [Hsm [HJ _]]; exact (conj Hsm HJ)|].
    apply (MSX W st Ai Kc rho1 tp1 HW HKc). intros tr md _. exact Hroom.
  - intros A ms kc HP Hkc HB. cbn beta. rewrite rw_call'. exact (HROOM A kc HP Hkc HB).
  -   intros Ai kc tr md HJ. destruct nd as [tv fr bd am]. cbn [nd_am nd_tv] in Ham, Hfew. subst am.
    pose proof (JAi_large_live_le0 segs AInv CST XGL ALA NP Kc rho0 P0f FB FF BX PA tv fr bd Ai kc rho tp tr md HJ) as LL. unfold sec_room. lia.
  -   intros Ai kc tr md HJ.
    pose proof (JAi_small_live_le AInv CST XGL NP Kc rho0 P0f FB FF BX PA nd Ai kc rho tp tr md HJ) as SL. unfold prim_room. lia.
  - intros E0. discriminate E0.
  - intros _. exact Tok.
Qed.
End Sum.
End WithSegs.
End DrvSiteS.

(* [comment removed for export] *)
Module DrvBox.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "list"; "prod"; "bool"; "length"; "true"; "app"; "nil"; "pair"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "ss_facts"; "valuation"; "SLit"; "sprop"; "holds"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "bxt"; "bsumV"; "BXok_d"; "LARGE_MIN"; "SECCAP"; "bud_pay"; "bxN"; "bd_wpos"; "bxK"; "bxS"; "bxV"; "BXnn"; "TVMAX"; "bd_below"; "bd_nn"; "bsumK"; "mkBX"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "of_nat"; "mul"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "NDA"; "ANone"; "JA"; "amode"; "ndesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nl.DrvBox"; "BXnn9"; "box_back"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "PRIM_LIVE_MAX"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "payA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "alloc_lawsA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymSummary SymEntail SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA SummaryA GlueA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface IfaceEx IfaceS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAM.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition box_back (BX BX' : bxt) (brest : list bitem) (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S22S26S1aVBX';A1S1aVBX;A1A2S22S26S25S1bVBX;A1S12Vbrest;Vrho;A2A2S1bVBX';A1A2S22S26S25S19VBX;A1S20Vbrest;Vrho;A2A2S19VBX';A1A2S22S1fVbrest;Vrho;A2S22S23S2S18Vbrest;A1S4A3S23S8S17VBX';A1S17VBX;A1A3A2A2A2A2A2").

Definition BXnn9 (BX : bxt) : Prop := ltac2:(tb__ "0|1|
S22S1cVBX;A1S22S26Z0S17VBX;A1M0A2S26S25G0S28S1dZ9A2A2S3cA2A2A2").

Section WithSegs.
Variable segs : list Segment.
Variable AInv : ltac2:(tb__ "0|0|
S3bScS0S35Q40A1A1S3dOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S40Vsegs;VAInv;VCST;A3").
Section Box.
Variable NP : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S0S1S1S8S8A2S8A2A1").
Variable PA : AA -> Prop.
Let JA : ltac2:(tb__ "0|0|
S11S3bOF_;S30S2bFnd;FPA;FBX;") := ltac2:(tb__ "0|0|
S2eVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;A9").

Lemma box_open_w : ltac2:(tb__ "0|3|
S11S0S1SaSaA2M0A1S0S1S1SaS8A2SaA2A1S0S10A1M1G1G1S32ScS0S35Q40A1A1S36S33RaA1S23S2S16SbS31R5A1A1SdZ0M2A1G2R8S5S10R7R6A3A5S4A3S3aSeSfR5A1SbS31R6A1A1A3S26S25S28S14S25S27S3S1S8S8A2VFB;A2A1S27S3G0RcA2A1A2A2S29S12RaR6A2S12R8R6A2A2A2S15A2S2aVsegs;VJA;ReVPA;S2cRdRcRbS2dA4A3R8R7R6R5A6S24S11S11S22S22S13Z9R1A2S34R10R1RbR9A4A2S2aVsegs;VJA;R1VPA;S2cRfReRcS2dA4A3RaR9R8R7A6A2LBX';A2F_;F_;F_;F_;F_;Fw;Ftp;Frho;FC;Fbrest;Fbdc;Fbd;Ffr;Ftv;FBX;").
Proof using ALA.
  intros BX tv fr bd bdc brest C rho tp w [[HV0 HK0] [HN0 HN9]] Hpay HF Hcap [Hsm (Ai & kc & HJ)].
  pose proof (JAi_large_live_le0 segs AInv CST XGL ALA NP Kc rho0 P0f FB FF BX PA tv fr bd Ai kc rho tp (w_tr w) (cfg_model (w_cfg w)) HJ) as LL.
  destruct (JAi_proj_BUD AInv CST XGL NP Kc rho0 P0f FB FF BX PA _ Ai kc rho tp _ _ HJ) as (HBU & HCK & Hkc).
  cbn [nd_bd nd_am] in HBU. pose proof HBU as (A1 & A2 & A3 & A4 & A5 & Hw & Hnn & B1 & B2).
  destruct (bud_pay_sound _ _ _ _ _ rho HF Hnn Hpay) as (P1 & P2 & _ & _ & _ & P6 & P7 & _).
  rewrite bsumV_app in P1. rewrite bsumK_app in P2. pose proof (uval_range rho (SLit 0)) as U0.
  assert (Hwc : bd_wpos bdc = true /\ bd_wpos brest = true).
  { unfold bd_wpos in *. rewrite forallb_app in P7. apply andb_prop in P7. exact P7. }
  assert (Hnc : bd_nn bdc rho /\ bd_nn brest rho) by (unfold bd_nn in *; apply Forall_app in P6; exact P6).
  destruct (bsum_nonneg bdc rho (proj1 Hwc) (proj1 Hnc)) as [S1 S2]. destruct (bsum_nonneg brest rho (proj2 Hwc) (proj2 Hnc)) as [S3 S4].
  pose proof (apot_range ANone rho) as [[R1 _] [R2 _]].
  unfold bxa in A1, A2, B1, B2. cbn [fst snd] in A1, A2, B1, B2. unfold bxV, bxK in HV0, HK0.
  set (BX' := mkBX (VMAX - aa_V Ai - bsumV bdc rho - fst (apot ANone rho), snd (bx2 BX) + bsumK brest rho) (LARGE_MIN * large_live Ai - aa_V Ai) (bxN BX)).
  assert (LM : LARGE_MIN * large_live Ai <= LARGE_MIN * (Z.of_nat (length FB) + Z.of_nat (length tv))) by (apply Z.mul_le_mono_nonneg_l; [unfold LARGE_MIN; lia | exact LL]).
  assert (EP : fst (apot ANone rho) = 0) by reflexivity.
  exists BX'. split; [split|].
  -   unfold BXok_d, BXok, BXnn, bxV, bxK, BX'. cbn [bx2 bxS bxN fst snd]. split; [split; [split; lia|lia]|]. split; [exact HN0|]. split; [lia | exact HN9].
  -   unfold box_back, bxV, bxK, BX', capK in *. cbn [bx2 bxS bxN fst snd]. repeat split; try lia; [exact (proj2 Hnc) | exact (proj2 Hwc)].
  - split; [exact Hsm|]. exists Ai, kc.
    apply (JAi_rebx AInv CST XGL NP Kc rho0 P0f FB FF BX BX' PA (NDA tv fr bd ANone) bdc Ai kc rho tp _ _); [|unfold BX'; cbn [bxN]; lia|exact HJ].
    intros _ _ _. cbn [nd_bd nd_am]. split.
    + unfold BUD, bxa, BX'. cbn [bx2 fst snd]. repeat split; try assumption; try lia; [exact (proj1 Hwc) | exact (proj1 Hnc)].
    + unfold capK, BX'. cbn [bxS]. lia.
Qed.

Lemma box_close : ltac2:(tb__ "0|1|
S11S11S0S10A1M0S0S1SaSaA2A1S0S1S1SaS8A2SaA2A1G0S2fS9S32ScScS0S35Q40A1A1S36S33RdA1S34ReRdRcR5A4S3eR8R6R5A3S23S2S1eR9ReA2S4A3S2aVsegs;VJA;R10VPA;S2cReRdRcRbA4A3R9R7R6R5A6S2aVsegs;VJA;R12VPA;S2cRfReS5S10RdR10A3RcA4A3RaR8R7R6A6F_;F_;F_;F_;F_;Fw;Ftp;Frho';Frho;FC;Fn;Fam;Fbdp;Ffr;Ftv;Fbrest;FBX';FBX;").
Proof using .
  intros BX BX' brest tv fr bdp am n C rho rho' tp w [[HV0 HK0] _] (K1 & K2 & K3 & K4 & K5 & K6) Hag Hb [Hsm (Ai & kc & HJ)].
  split; [exact Hsm|]. exists Ai, kc.
  apply (JAi_rebx AInv CST XGL NP Kc rho0 P0f FB FF BX' BX PA (NDA tv fr bdp am) (bdp ++ brest) Ai kc rho' tp _ _); [|lia|exact HJ].
  cbn [nd_bd nd_am]. intros HBU HCK Hkc. pose proof HBU as (A1 & A2 & A3 & A4 & A5 & Hw & Hnn & B1 & B2).
  pose proof (apot_range am rho') as [[R1 _] [R2 _]].
  rewrite <- (bsumV_agree n rho rho' brest Hag Hb) in K2. rewrite <- (bsumK_agree n rho rho' brest Hag Hb) in K3.
  pose proof (bd_nn_agree n brest rho rho' Hag Hb K4) as K4'.
  unfold bxa, bxV, bxK, capK in *. cbn [fst snd] in *. split; [|lia].
  unfold BUD. cbn [fst snd]. rewrite bsumV_app, bsumK_app.
  split; [lia|]. split; [lia|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
  split; [unfold bd_wpos in *; rewrite forallb_app, Hw, K5; reflexivity|].
  split; [unfold bd_nn in *; apply Forall_app; split; assumption|]. lia.
Qed.

Lemma box_open_T : ltac2:(tb__ "0|3|
S36OF_;S11S0S1SaSaA2M0A1S0S1S1SaS8A2SaA2A1S0S10A1M1G1G1S32ScS0S35Q40A1A1S39S33RaA1S23S2S16SbS31R5A1A1SdZ0M2A1G2R8S5S10R7R6A3A5S4A3S3aSeSfR5A1SbS31R6A1A1A3S26S25S28S14S25S27S3S1S8S8A2VFB;A2A1S27S3G0RcA2A1A2A2S29S12RaR6A2S12R8R6A2A2A2S15A2F_;S11S13Z9R1A2S34RfR2RaR8A4S38Vsegs;R11S2aVsegs;VJA;R3VPA;S2cRfReRcS2dA4A3RaR9R8A5R7A4F_;F_;FBX';S38Vsegs;RfS2aVsegs;VJA;ReVPA;S2cRdRcRbS2dA4A3R8R7R6A5R5A4F_;F_;F_;F_;FQ;Ftp;Frho;FC;Fbrest;Fbdc;Fbd;Ffr;Ftv;FBX;Fok;").
Proof using ALA.
  intros ok BX tv fr bd bdc brest C rho tp Q HBX Hpay Hcap HT. apply triple_factsA. intros HF.
  eapply (triple_conseq (P := fun w => exists BX', (BXok_d 9 BX' /\ box_back BX BX' brest rho) /\ SPA segs (JA BX' PA (NDA tv fr bdc ANone)) C rho tp w));
    [intros w HS; exact (box_open_w BX tv fr bd bdc brest C rho tp w HBX Hpay HF (Hcap HF) HS) | intros w' Hw'; exact Hw' |].
  apply triple_ex. intros BX'. apply triple_pure. intros [H1 H2]. exact (HT BX' H1 H2).
Qed.
Lemma box_open_Te : ltac2:(tb__ "0|3|
S11S0S1SaSaA2M0A1S0S1S1SaS8A2SaA2A1S0S10A1M1G1G1S32ScS0S35Q40A1A1S36OF_;S33RaA1S23S2S16SbS31R5A1A1SdZ0M2A1G2R8S5S10R7R6A3A5S4A3S3aSeSfR5A1SbS31R6A1A1A3S26S25S28S14S25S27S3S1S8S8A2VFB;A2A1S27S3G0RcA2A1A2A2S29S12RaR6A2S12R8R6A2A2A2S15A2F_;S11S13Z9R1A2S34RfR2RaR8A4S37Vsegs;S2aVsegs;VJA;R3VPA;S2cRfReRcS2dA4A3RaR9R8A5R7A3F_;F_;FBX';S37Vsegs;S2aVsegs;VJA;ReVPA;S2cRdRcRbS2dA4A3R8R7R6A5R5A3F_;F_;F_;F_;FQ;Ftp;Frho;FC;Fbrest;Fbdc;Fbd;Ffr;Ftv;FBX;").
Proof using ALA.
  intros BX tv fr bd bdc brest C rho tp Q HBX Hpay Hcap HT. apply etriple_factsA. intros HF.
  eapply (etriple_conseq (P := fun w => exists BX', (BXok_d 9 BX' /\ box_back BX BX' brest rho) /\ SPA segs (JA BX' PA (NDA tv fr bdc ANone)) C rho tp w));
    [intros w HS; exact (box_open_w BX tv fr bd bdc brest C rho tp w HBX Hpay HF (Hcap HF) HS) | intros w' Hw'; exact Hw' |].
  apply etriple_ex. intros BX'. apply etriple_pure. intros [H1 H2]. exact (HT BX' H1 H2).
Qed.

Lemma payA_self : ltac2:(tb__ "0|1|
S0SeA1S0S10A1S23S2S18R1A1S4A3S3fVNP;Vrho0;VP0f;R3SdZ0M0A1G0R2S5S10R2S6S10A1A3A8F_;Fbdc;Ffacts;").
Proof using .
  intros facts bdc Hw. unfold payA, pay_okF. rewrite app_nil_r. split; [exact Hw|]. split; [lia|].
  intros rho _ _ _ Hn. unfold pay_sem. pose proof (uval_range rho (SLit 0)) as U0.
  assert (E0 : uval rho (SLit 0) = 0) by reflexivity. rewrite E0. repeat split; try lia. exact Hn.
Qed.
End Box.
End WithSegs.

Lemma BXnn_mk00 : ltac2:(tb__ "0|1|
S8S33S21S7S8S8Z0M0G0A4R1G0A3A1FS;").
Proof. intros S. unfold BXnn9, BXnn, bxV, bxK, TVMAX, PRIM_LIVE_MAX. cbn [bx2 bxN fst snd]. lia. Qed.
End DrvBox.

