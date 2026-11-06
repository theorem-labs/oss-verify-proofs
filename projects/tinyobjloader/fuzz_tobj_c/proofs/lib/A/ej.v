(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From Stdlib Require FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_vn Asan_memcpy_contract.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ListCommitA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fn.

(* [comment removed for export] *)
Module Lib_tess_polygon_chk4.

From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SummaryA EntailA CFGA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.JcertCutA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_tess_scale2d.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_tess_scale2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e1.Lib_tess_run2d_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_tess_polygon_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_tess_polygon_cstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_tess_polygon_chk0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import TessPolygonAddr.
Lemma cc_19 : CC 19 T_sc3 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_20 : CC 20 T_sc4 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_21 : CC 21 T_r2 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_22 : CC 22 Kaa4 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_23 : CC 23 Kb08 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_24 : CC 24 Kb14 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_25 : CC 25 Kd10 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_26 : CC 26 Kb64 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_27 : CC 27 Kd60 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_28 : CC 28 Ktail = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_29 : CC 29 C_fin = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_30 : CC 30 C_b6cK = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_31 : CC 31 T_sfI = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_32 : CC 32 T_sfK = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_tess_polygon_chk4.

(* [comment removed for export] *)
Module Lib_build_line_index_rom_call.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_base"; "ax_X"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "pair"; "prod"; "option"; "Some"; "andb"; "None"; "false"; "fst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_next"; "sobj"; "sv"; "SLit"; "sprop"; "ss_facts"; "holds"; "sv_eqb"; "@Corelib.Init.Logic"; "eq"; "and"; "True"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkPA"; "entails_frA"; "J_ofPA"; "xs_framed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "nd_tv"; "JA"; "JAi"; "JAk"; "NDA"; "nd_am"; "nd_bd"; "nd_below"; "nd_fr"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@Stdlib.Lists.List"; "In"; "forallb"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "SHADOW_OFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "keptR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "payA"; "site_okA"; "xrs_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "JL_pure"; "J_pure_pre"; "alloc_lawsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface IfaceEx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.
Variable AInv : ltac2:(tb__ "0|0|
S1dSfS4S3eQ40A1A1S23OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S55Vsegs;VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S1bS49VCST;R1A2S19S4aZ0R2A2S4bR2S47A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S1bS49VXGL;R1A2S19S4aZ0R2A2S4bR2S47A2A2F_;Fa;").
Section Sum.
Variable NP : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S4S8S8S1bS1bA2S1bA2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Hypothesis HKc : Kc_ok Kc.

Let JAi : ltac2:(tb__ "0|0|
S30S1dS1bS1fFkc;FAi;Fnd;") := ltac2:(tb__ "0|0|
S33VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").
Let JA : ltac2:(tb__ "0|0|
S30S1fFnd;") := ltac2:(tb__ "0|0|
S32VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").
Let JAk : ltac2:(tb__ "0|0|
S30S1dS1fFAi;Fnd;") := ltac2:(tb__ "0|0|
S34VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").
Let site_okA : ltac2:(tb__ "0|0|
S0S2fS4S11A1SfS30S9S1bA1S1dS22OF_;F_;OFextra;Fx;Fnd;Frho;FR;Fs;FCl;") := ltac2:(tb__ "0|0|
S51VAInv;VCST;VXGL;VNP;Vrho0;VP0f;VFB;VFF;A8").
Let payA : ltac2:(tb__ "0|1|
S4S14A1S12S1bS4S45A1M0G0OFbto;Fbfrom;FcostK;FcostV;Ffacts;") := ltac2:(tb__ "0|0|
S50VNP;Vrho0;VP0f;A3").
Let call_checkTA := call_checkTA NP.
Let cmaddrA := cmaddrA CST.
Let robjs_okA := robjs_okA CST.

Ltac chain_same_tv Hlink Hnb :=
  cbn zeta; intros ? ? _ _ Hut;
  eapply untracked_agree; [eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch] | | exact Hut];
  exact (proj1 (nd_below_split _ _ Hnb)).

Section CallT.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S1fS0SfS4S3eQ40A1A1S25S40S14S16R3A1S15S1R4A1A1A3VTR;S1eVsegs;R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S25S25S25S26R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S1fS1fS0S0S2fS4S11A1M0S4S8S0S27A2M1A1S4S8S12S12A2M2A1S25SfS4S3eQ40A1A1M3G2S3cG2R1R5A3S3cG2R2S3RbA1A3F_;Fr;S18S9G0A1S2aRaR9R8A3SaG0R7A2A3S18S5S29RbRaR9R8S3fG1S0SeS0S27A2R7A4A5S6A3SfG3VTR;S1eVsegs;RfRdR2R1A5S28Vsegs;S10S1RdA1A1R2R1RaA5A2Ftp1;Frho1;S4S24A1M4S22S23S20Vsegs;R9R8R10S7G4S3aR3S3bR2R1A2A4A5R13RaR9R4R2A4R13S2eS2dRbRfS21R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S0S27G4S22S23SfG3G4S22S23S3cG1S7S0S27RaR9A4R14A3S20Vsegs;R12R11R19S7G4S3aR9S3bR8R7A2A4A5R1cR13R12RaR8A4S42S10S1R1aA1A1S2eS2dR14R18S21R9R13RaA3A3R19A2R8A3S20Vsegs;R9R8ReS7G4S3aR7S3bR6R5A2A4A5ReS2eS2dR16R1aS21RbR15RcA3A3R1bA2R15RaR9R8R6A6S19S4cR17S21RcR16RdA3R1bR1cR1dR10R1eR19RbA9SfS43R18S21RdR17ReA3R1cR1dS1R1eA1S1R1fA1S1R11A1R1RcA9VTR;S1eVsegs;S2bR11S2eS2dR19R1dS21ReR18RfA3A3R1eA2R18RdRcA5S4dR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S1eVsegs;R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Theorem purec_callT_k_xp : ltac2:(tb__ "0|5|
S1dSfOF_;F_;S0S4S0A1S0S2fS4S11A1M0SfS4S3eQ40A1A1M1S30S4S45A1S25S1dSfG1VTR;S1eVsegs;SfG1S4S24A1M2S23S19S54VAInv;R7VKc;R4R3R2R1A7R12R7R4A2A2Lm;Lt;Lp;Lr;RdR2R1A5S28Vsegs;S41R2R1S3fS0S8S0S27A2S0S7S0S27R1S53VAInv;VCST;VXGL;R4VKc;A5A4LL;RcA4A5A2Ftp1;Frho1;FAi;S18S1cS10S1RbA1A1S41A3S18S12S2RcA1S13S48A1A3S18S9G0A1S2aRbRdRaA3SaG0R9A2A3S18S5S29RcReRbRaRdA5S6A3S18S5Vcall_checkTA;RcA1S6A3S18S5S56VNP;S10S1ReA1A1A2S6A3S18S5S38S10S1RfA1A1RaA2S6A3S18S5S46S10S1R10A1A1RaA2S6A3VpayA;S15S1R11A1A1S13Z0M3A1G3S37RcA1RbA5S18S5S3dS0S0SbSbG0S5Lx;S44S1R15A1S1R1A1A2S6S11G0SdLl;Ls0;X4x2S2cR15R1A2A2S17S2R1A1S2R15A1A2A2LL;R13A3S6A3Vsite_okA;R13R12R11R10ReScS1bA1M4S1dS22S1aLms;LAi;A7S1dG2S22S23S20Vsegs;R15R14R18S7G2S3aR3S3bR2R1A2A4A5VAInv;R5R16R15R2A4S52VCST;VXGL;R6G4R17S3R1aA1A6R1eR7S2eS2dR18R19S21R4R17R5A3A3R1aA2A2F_;F_;F_;Fmd;Fms;Ftr;FAi;S0SfG1S3cS0R3R19A3S42S10S1R19A1A1R16R3A3S4eR17S31R15A1R4A3VTR;S1eVsegs;VJA;S35S31R16A1S39R16A1R15S36R16A1A4A1S4fR1dR1bR1aR19R6A5R5R4A5R14A2F_;F_;F_;Ftp';Frho';FL;VTR;S1eVsegs;VJA;R11A1R16R13R12A5RfA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Fnd;Ftp;Frho;FR;Fs;FCl;FLs;FPre;FXP;").
Proof using ALA HCST HXGL HKc TR_callP TR_ex TR_facts TR_pre.
  intros XP Pre Ls Cl s R rho tp nd bd' Q CALLEE HNF HbP He Hchk Htp Hnf Hnb Hbb HPAY Hshape HSITE HXP Tcont.
  apply Pos.leb_le in Hnf.
  apply TR_facts. intros HF.
  apply (TR_ex AA (JAk nd)). intros Ai. apply (TR_ex Z (JAi nd Ai)). intros kc.
  eapply (TR_callP (JAi nd Ai kc) (fun r p t m => J_pure_pre AInv Ai Kc r p t m /\ XP Ai r) Cl Pre s R
            (map (fun L => (L, JL_pure AInv CST XGL Ai Kc)) Ls) (ax_X Cl) Q rho tp (fun r H => H) He).
  - rewrite map_map. cbn [fst]. rewrite map_id. exact Hchk.
  - intros rho1 tp1. rewrite HNF. apply CALLEE.
  -
    intros tr ms md Hsm HJ. pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    destruct (HSITE Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA NP rho0 Ai s rho Hav HT Htp)) as (HRok & HX & _).
    split; [|exact (HXP Ai tr ms md Hsm HM HX)].
    split; [eapply (AInv_absorb segs AInv CST ALA HCST); [exact HM | exact HRok]|]. split; [exact Hk|]. split; [eapply (tp_of_TPA NP rho0); eauto | exact (top_of_TPA NP rho0 Ai s rho _ _ Hav HT Htp)].
  -
    intros L JL tr ms md rhoL tpL tr' ms' md' HinL Hsm HJ Hag1 HsmL HJL.
    pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    destruct (HSITE Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA NP rho0 Ai s rho Hav HT Htp)) as (HRok & HX & _).
    pose proof (entails_frA_base _ _ _ _ SHADOW_OFF He HbP) as HbC.
    apply in_map_iff in HinL as (L0 & Heq & HinL). injection Heq as HJLe HL. subst L JL.
    pose proof (proj1 (forallb_forall _ _) Hshape L0 HinL) as HS. apply andb_prop in HS as [HS HbL]. apply andb_prop in HS as [Hnonew Hxf].
    apply sv_eqb_sound in HbL. rewrite HbP in HbL.
    assert (NONEW : forall o', In o' (new_objs (ax_S Pre) (ax_S L0)) -> False).
    { intros o' Hin'. destruct (new_objs (ax_S Pre) (ax_S L0)); [destruct Hin' | discriminate]. }
    destruct HJL as (HM2 & Htp2 & Hkept2 & Hk2).
    assert (Hsub : forall a, cmaddrA Ai None a -> cmaddrA Ai None a) by (intros a H; exact H).
    split.
    * split; [split; [exact (KEPT_stepA segs AInv CST XGL ALA Ai Ai None rho rhoL _ s R _ _ _ HM HRok Hsub Hkept2)|]|split].
      -- intros o' oR Hin' _. exfalso. exact (NONEW o' Hin').
      --
         intros r a j oR Hr Ha Hj HoR Hrng.
         unfold xs_framed in Hxf. pose proof (proj1 (forallb_forall _ _) Hxf r Hr) as Hrp. apply existsb_exists in Hrp as (rp & HinP & Heqr).
         apply xr_eqb_sound in Heqr. subst rp.
         pose proof Hsm as (HsmS & _ & HwfC & HshC & _).
         assert (HXcov : forallb (fun r0 => xr_covered (ss_facts (ax_S Cl)) (ax_X Cl) (xr_subst s r0)) (ax_X Pre) = true /\ axwf Pre = true).
         { clear - He. rewrite entails_frA_ref_eq in He. unfold entails_frA_ref in He. destruct (entails_fr (ax_S Cl) (ax_S Pre) s); [|discriminate].
           match type of He with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
           apply andb_prop in Hc as [Hc Hwf]. apply andb_prop in Hc as [Hc _]. auto. }
         destruct HXcov as [HXcov HwfP].
         pose proof (xr_covered_sound rho (ss_facts (ax_S Cl)) (ss_objs (ax_S Cl)) (bv_unsigned (eval rho (ax_base Cl))) (ax_X Cl) (xr_subst s r)
                       HF (proj1 (forallb_forall _ _) HXcov r HinP) HshC) as Hok.
         unfold axwf in HwfP. apply andb_prop in HwfP as [HwfX _]. pose proof (proj1 (forallb_forall _ _) HwfX r HinP) as Hrb.
         unfold xr_below in Hrb. apply andb_prop in Hrb as [Hrb1 Hrb2].
         assert (EV : forall e, sv_below (ss_next (ax_S Pre)) e = true -> eval rhoL e = eval rho (sv_subst s e)).
         { intros e He0. rewrite <- (eval_agree_vals _ _ _ e Hag1 He0). rewrite <- eval_subst. apply eval_absorb. }
         destruct r as [b l]. cbn [fst snd] in Ha, Hrb1, Hrb2. rewrite (EV b Hrb1), (EV l Hrb2) in Ha.
         unfold xr_ok, xr_subst in Hok. cbn [fst snd] in Hok. rewrite <- !eval_subst in Hok || idtac.
         destruct Hok as (_ & _ & Hok). destruct (Hok a ltac:(rewrite !eval_subst; rewrite !eval_subst in Ha || idtac; exact Ha)) as (_ & _ & Hwd & _).
         destruct (Hwd j Hj) as [Hout _].
         rewrite HbL in Hrng. rewrite HbC in Hout. cbn [eval] in Hrng, Hout.
         exact (proj1 (Forall_forall _ _) Hout oR (proj2 (proj2 (proj2 (proj2 (entails_frA_sound segs Cl Pre s R rho tp tr ms md He Hsm)))) oR HoR) Hrng).
      -- eapply (caller_X_kept segs AInv CST XGL ALA HCST HXGL Ai Ai None rho tp md R (vms md tp ms) s rhoL Cl); eauto.
         all: try (eapply (xrs_range segs AInv CST XGL ALA HCST HXGL); eauto). all: intros o' Hin'; exfalso; exact (NONEW o' Hin').
    * intros rho' Hlink.
      assert (HagP : agree_vals (ss_next (ax_S Cl)) rho (rho_patch rho' (patchf rho rho' R))).
      { eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch]. }

      assert (KR : keptR rho (nd_tv nd) (rho_patch rho' (patchf rho rho' R))).
      { intros t0 z Ht0 Hnz0 Hz. destruct (proj1 (Forall_forall _ _) HN t0 Ht0 Hnz0) as (_ & Hl0 & _).
        exact (proj1 (live2_kept segs AInv CST XGL ALA HCST Ai Ai None rho rho' rhoL (vms md tp ms) s R tp md _ _ HM HRok Hkept2 (proj1 (proj2 Hlink)) Hl0 Hl0) z Hz). }
      eapply TR_pre; [ | apply (Tcont L0 (rho_patch rho' (patchf rho rho' R)) tpL HinL HagP KR)].
      intros w [Hsm' HJ']. cbn [J_ofPA] in HJ'.
      destruct HJ' as (HM3 & Htp3 & Hkept3 & Hk3).
      destruct w as [trw [msw mdw]]. cbn [w_tr w_cfg fst snd cfg_model] in *.
      split; [exact ((cont_smatchA segs) Cl Pre _ s R rho rho' tp tpL tr ms md _ He Hsm (proj1 Hlink) Hsm')|].
      exists Ai, kc.
      destruct (law_budget _ _ _ ALA Ai _ _ _ HM3) as (_ & _ & HV0 & HKm0 & HKf0).
      pose proof Hnb as Hnb0. destruct (nd_below_split _ _ Hnb) as (Hbt & _ & _ & _).
      eapply (cont_JAi segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0f FB FF BX PA Cl Pre L0 s R rho tp tr ms md rhoL tpL trw mdw rho' nd Ai kc Ai None
                _ bd' (SLit 0) 0 He Hsm Hnf Hnb0 Hbb HJ HRok Hlink HM3 Hk3 Hsub); try assumption; try reflexivity.
      -- pose proof (uval_range rho (SLit 0)). lia.
      -- lia.
      -- cbn zeta. split; [|split].
         ++ apply (tvinA_agree FB Ai (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HN].
         ++ apply (tvd_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HD].
         ++ apply (tvz_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HZ].
      -- intros b m Hb _ _. exact Hb.
      -- chain_same_tv Hlink Hnb0.
      -- cen_same_tvG Hlink Hnb0 (eq_refl (aa_live Ai)).
      -- capN_sameG HCNi Hlink Hnb0 (eq_refl (aa_live Ai)).
Qed.
End CallT.
End Sum.
End WithSegs.
End Lib_build_line_index_rom_call.

(* [comment removed for export] *)
Module Lib_realloc_rom_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "bd_subst"; "bitem"; "bud_le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "ss_facts"; "holds"; "sobj"; "sprop"; "SLit"; "SVar"; "rm"; "ss_next"; "SPUle"; "SAlu"; "ss_objs"; "ob_base"; "sv_eqb"; "sstate"; "ob_hi"; "ob_lo"; "obj_range"; "sprop_below"; "swf"; "SPBranch"; "agree_below"; "eval"; "rw"; "obj_wf"; "soff"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_X"; "ax_setS"; "@Corelib.Init.Datatypes"; "bool"; "list"; "prod"; "true"; "pair"; "nil"; "nat"; "option"; "cons"; "Some"; "fst"; "snd"; "app"; "false"; "None"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_realloc_rom"; "vK"; "kb16"; "vP"; "tv1"; "vQ"; "ndR"; "vKn"; "bd1"; "pN"; "pls"; "B32"; "X_a2"; "q1"; "E_fa2"; "E_fp"; "X_step"; "tv0"; "E_fa1"; "E_freeT"; "X_a1"; "X_cp0"; "X_p"; "X_s"; "s_f"; "s_m"; "C_0"; "E_fc"; "E_free"; "E_ft"; "E_m"; "R_m"; "X_cp0f"; "X_t"; "bd0"; "s_cp0"; "s_post"; "s_step"; "vA"; "P0_rr"; "P_okX"; "R_f"; "VQ"; "X_c"; "X_cp0c"; "free_facts"; "step_facts"; "tv2"; "O_fs"; "P_fail"; "P_ok"; "Pre_m"; "Pre_rr"; "X_r"; "cp0_facts"; "cutsE"; "exitsE"; "tiles2"; "tvP"; "two47"; "E_ff"; "FUEL_rr"; "Pre_f"; "T_free"; "T_mnull"; "T_mok0"; "X_f"; "cutpcs_rr"; "eoff"; "sel7"; "sel8"; "vF0"; "vF1"; "vPn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "nd_below"; "JA_pre"; "nd_tv"; "JA"; "ffinA"; "ok_frameKA"; "tvinA"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "AE_A"; "ulink"; "L_free"; "unwind_stopJ"; "JL_free"; "J_alloc_pre"; "J_free_pre"; "L_malloc_null"; "L_malloc_ok"; "Posts_malloc"; "Pre_free"; "Pre_malloc"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@Stdlib.Lists.List"; "In"; "nth_error"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub_get"; "wsub_id_below"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjArena"; "rd64"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Lib_realloc_rom_pf.Sum"; "Phi1"; "ptr0"; "Phi0"; "Phis"; "Posts_rr"; "K0"; "Kn0"; "Phi2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tnz"; "tvv"; "tv_sub_eqb"; "FBx"; "remove_nth"; "tvd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXSelect"; "AXSplit"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Lib_realloc_rom_pf"; "extraAL"; "o_src"; "extraFS"; "o_dstE"; "o_dstX"; "PDk_rr"; "Psi_fail"; "Psi_ok"; "extraX"; "o_nb"; "o_restX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "JAF"; "efmeasA"; "carve_site_chk"; "carve_ent_stateA"; "phiK"; "JLAP"; "ejcertAF"; "ent_obj"; "phi_reads"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "carve_stateA"; "drop_lastA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "is_shadowZ"; "site_okA"; "cmaddrA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CellTile"; "tiles_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "FFx"; "pclMA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "PostsCk"; "keptR"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj SymCall ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena CellTile ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxArrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_realloc_rom.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import RRAddr.

Definition o_src (q : sv) : sobj := ltac2:(tb__ "0|0|
SecS4dS46S45Vq;A1A2PadA2").
Definition o_restX : sobj := Eval vm_compute in nth 2 (ss_objs (ax_S X_s)) O_D.
Definition o_dstX : sobj := Eval vm_compute in last (ss_objs (ax_S X_p)) O_D.
Definition o_dstE : sobj := Eval vm_compute in last (ss_objs (ax_S E_fp)) O_D.
Definition o_nb : sobj := Eval vm_compute in nth 1 (ss_objs (ax_S X_cp0)) O_D.

Lemma T_mnull_eq : ltac2:(tb__ "0|0|
S1S2dSf3S76S61S5cS62Sa4S9dS36S9eA1S9cA3A5S83A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mok0_eq : ltac2:(tb__ "0|0|
S1S2dSf3S76S61S5cS62Sa5S9dS36S9eA1S9cA3A5S84A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_free_eq : ltac2:(tb__ "0|0|
S1S2dSf3S81S56S5bS6cS9fS9dS36S9eA1S9cA3A5S82A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma X_eqs : ltac2:(tb__ "0|8|
S0S1S38S1aA1Sf7S2cS53A1S7cA2S3aS1aS2cS64A1A2A3S0S1S38S2dA1M0Sd4S85S39Sd3Sd6U1S11Z10A1A2S36Sd3A1M1A3A2S3aS2dS5aA2A3S0S1S38SfA1Sb6SfS17S2cS5aA1M2A1U2M3A3S3aSfSe4A2A3S0S1S2dS30S5aSfcG2G3S73S12S4cA1S50S4aA3A3A2S78A3S0S1G0Sd4S78S39Sd3Sd5S89A1G1A3A2S3aS2dS59A2A3S0S1S32SfA1M4S17S2cS59A1A1S3dSfS17S2cS57A1A1M5S39SfSdeS36SfA1M6A3A3A3S0S1S2dSefS59G5A2S57A3S0S1G4G5S3dSfS17S2cS4fA1A1M7S39SfSdbS48A1G6A3A3A3S0S1S2dSefS57G7A2S4fA3S1S2dSe8S4fS4dS46S45S50A1A2A2S6eA3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma E_eqs : ltac2:(tb__ "0|4|
S0S1S38S1aA1Sf7S2cS5fA1S7cA2S3aS1aS2cS60A1A2A3S0S1S38S2dA1Sd4S7fS39Sd3Sd5S88A1S36Sd3A1A3A2S3aS2dS52A2A3S0S1S32SfA1M0S17S2cS52A1A1S3dSfS17S2cS55A1A1M1S39SfSddS36SfA1M2A3A3A3S0S1S2dSefS52G1A2S55A3S0S1G0G1S3dSfS17S2cS51A1A1M3S39SfSdbS48A1G2A3A3A3S0S1S2dSefS55G3A2S51A3S1S2dSeeS51S46S45S44A1A3S5eA3A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma cp0_eqs : ltac2:(tb__ "0|0|
S0S1S2dSe8S63S4dS46S45S11Z0A1A1A2A2S6fA3S1S38SfA1Sb6SfS17S2cS58A1A1U1A3S3aSfSe3A2A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition extraAL (o : sobj) : bool := ltac2:(tb__ "0|1|
S31S31L_;M0S19S18Vo;A1S69A2G0S19S1cVo;A1S11Z0A1A2S19S1bVo;A1S11Z30A1A2S3eX31x2S3eX31x2").
Definition extraFS (c : sv) (o : sobj) : bool := ltac2:(tb__ "0|1|
S31S31L_;M0S19S18Vo;A1S16Sd7S12S4cA1S45Vc;A1A3A2G0S19S1cVo;A1S11Z0A1A2S19S1bVo;A1S45S16Sd8S4aVc;A3A1A2S3eX31x2S3eX31x2").
Definition extraX (o : sobj) : bool := ltac2:(tb__ "0|0|
S31S31L_;SdaVo;A1S34SdcS50Vo;A2X31x2").

Lemma chk_X : ltac2:(tb__ "0|2|
S0S1S31S1fS2cSeeS4fS4dS46S45S50A1A2S11Z10A1A3A1A1S34A3S0S1S31Se7S4fS47S36S33S33ScS5A2ScA2A1U1Se2A5S34A3S0S1S31S93S14S2cS4fA1A1S49S47S4bA2M0A2S34A3S0S1S31S2eS6eS5dS68A3S34A3S0S1S31SbeS68S90A2S34A3S0S1S31ScfS68S47S47A3S34A3S0S1S31S93S14S2cS6eA1M1A1G0A2S34A3S0S1S31SaSdG1A1S8S68S4bA2S4bA3S34A3S0S1S31S24S14S2cS5aA1A1S73S12S4cA1S50S4aA3A2S34A3S1S31Sb7S10S1eS14S2cS64A1A1A1S71A3S34A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma chk_E : ltac2:(tb__ "0|2|
S0S1S31S1fS2cSeeS51S46S45S44A1A3A1A1S34A3S0S1S31Se7S51S47S36S33S33ScS5A2ScA2A1U1SdaA5S34A3S0S1S31S2eS5eS56S36S33S6ScA2A1M0A3S34A3S0S1S31ScfG0S47S47A3S34A3S0S1S31S93S14S2cS5eA1M1A1S49S47S4bA2A2S34A3S0S1S31SaSdG1A1S8G0S4bA2S4bA3S34A3S1S31Sb7S10S1eS14S2cS60A1A1A1S70A3S34A3A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma chk_cp0 : ltac2:(tb__ "0|2|
S0S1S31S1fS2cSeeS63S4dS46S45S11Z0A1A1A2S11Z10A1A3A1A1S34A3S0S1S31Se7S63S47S36S33S33ScS5A2ScA2A1U1SdaA5S34A3S0S1S31S93S14S2cS63A1A1S49S47S4bA2M0A2S34A3S0S1S31S2eS6fS5dS66A3S34A3S0S1S31SbeS66S90A2S34A3S0S1S31ScfS66S47S47A3S34A3S0S1S31S93S14S2cS6fA1M1A1G0A2S34A3S0S1S31SaSdG1A1S8S66S4bA2S4bA3S34A3S1S31Sb7S10S1eS14S2cS58A1A1A1S79A3S34A3A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma chk_post : ltac2:(tb__ "0|2|
S0S1S31S2eS6bS75S67A3S34A3S0S1S31SbeS67S90A2S34A3S0S1S31ScfS67S72S7dA3S34A3S0S1S31S93S14S2cS6bA1M0A1S49S72S36S9A1M1A2A2S34A3S1S31SaSdG0A1S8S67G1A2G1A3S34A3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Ltac meas := unfold efmeasA; cbn [ef_rank ef_var fst snd];
  match goal with |- context [bv_unsigned (eval ?r ?e)] => pose proof (urange (eval r e)); lia end.
Tactic Notation "innth" integer(k) := do k right; left; reflexivity.

Lemma kb16_exact : ltac2:(tb__ "0|0|
SbScS26S7R2R1A2S4eA2S1S5S7R3S45R2A1A2S29Z10S7R3R2A2A2A3F_;Fe;Frho;").
Proof. intros rho e H. unfold kb16, B32 in *. apply uval_mul_lit; lia. Qed.

Lemma VQ_val : ltac2:(tb__ "0|1|
SbS5S0S26Z0R1A2S26R1Z20M0A2A2S28S7R3S48A2S7R3S44A2A2S26S7R4S44A2S4eA2S1S5S7R5S6dR4A1A2S2bS29G0S2bS27S27S7eZ1A2S7R5S44A2A2S7R5S48A2A2A2R4A2A3F_;F_;F_;Fc;Frho;").
Proof.
  intros rho c Hc HqK HK. unfold VQ, two47, B32 in *. pose proof (uval_range rho vQ) as RQ. pose proof (uval_range rho vK) as RK.
  assert (EA : uval rho (SAlu ALU_ADD (SLit (2 ^ 47 + 1)) vK) = 2 ^ 47 + 1 + uval rho vK).
  { rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity. }
  assert (ES : uval rho (SAlu ALU_SUB (SAlu ALU_ADD (SLit (2 ^ 47 + 1)) vK) vQ) = 2 ^ 47 + 1 + uval rho vK - uval rho vQ).
  { unfold uval in *. rewrite U_sub. rewrite EA. unfold M64v. apply Z.mod_small. lia. }
  assert (EM : uval rho (SMd M_MUL (SLit 32) (SAlu ALU_SUB (SAlu ALU_ADD (SLit (2 ^ 47 + 1)) vK) vQ)) = 32 * (2 ^ 47 + 1 + uval rho vK - uval rho vQ)).
  { rewrite uval_mul_lit by (rewrite ?ES; lia). rewrite ES. reflexivity. }
  unfold uval in *. rewrite U_sub, U_lit, EM. unfold M64v. rewrite (Z.mod_small c) by lia. apply Z.mod_small. lia.
Qed.
Lemma meas_VQ : ltac2:(tb__ "0|2|
S2dS91S37S5S5SbS0S26Z0R2A2S26R2Z20M0A2A2S28S7R2S48A2S7R2S44A2A2S26S7R3S44A2S4eA2S1S5Se6S35S33S33S2dS91A2M1S37A2S33S5ScA2S35G1S37S35S2dS91R9R8A4R7A4S35S5ScR6S6dR5A1A4A4R4A2S27S29R6S2aZ2Z40A2A2S2bS29G0S2bS27S27S7eZ1A2S7R4S44A2A2S7R4S48A2A2A2R5A2A2A3F_;F_;F_;Frho;Fc;Frk;Fk;Fnd;FT;").
Proof. intros T nd k rk c rho Hc HqK HK. unfold efmeasA. cbn [ef_rank ef_var fst snd]. change (bv_unsigned (eval rho (VQ c))) with (uval rho (VQ c)). rewrite (VQ_val rho c Hc HqK HK). reflexivity. Qed.

Lemma blocks_arith : ltac2:(tb__ "0|17|
SbSeR1S20Sd9S48S44A3A2SeR2S15S48S11S4eA1M0A2A2SeR3S15S11Z1M1A1S44A2A2SeR4S20Sd9S44S4aA3A2SeR5S15S4aG0A2A2SeR6S15S11Z1000M2A1M3S12S4cA1M4A2A2SeR7S15S16Sd7G4S45S4aA1M5A3S11Z7fffff800000M6A1M7A2A2SeR8S15G3S46A2A2SeR9S15S16Sd7S46S45S44A1M8A3S12P1eA1M9A2A2SeRaS15G9G7A2A2SeRbS15S46S11Z800000000000A1A2A2SeRcS15G4G7A2A2SeRdS15G5G0A2A2S0S28S7ReS48A2MaS7ReS44A2MbA2S0S28GbS7ReS4aA2McA2S0S26S29Z10MdGcA2MeS4eA2S0S26G1GbA2S0S1S5S7ReS45S48A1MfA2S29GdGaA2M10A3S0S1S5S7ReG8A2S29GdGbA2M11A3S0S1S5S7ReG5A2GeA3S0S5S0S26Z0R1A2S26R1Z40A2A2S1S5S7R10S87R2A1A2S27S29GdS7R10S48A2A2R2A2A3F_;Fj;S0S1S5S7ReS50A2S27GaG1A2A3S0S1S5S7ReS45S50A1M12A2S27G10GdA2A3S0S1S5S7ReS16Sd7S16Sd8G8GfA3S11N10A1A3A2S2bS2bG11G10A2GdA2A3S0S26G2S7ReG4A2M13A2S0S26S27G13GeA2G6A2S0S26G2S7ReS46A2M14A2S0S26S27G14G11A2G6A2S0S1S5S7ReS4dG4GfA2A2S27G13G10A2M15A3S0S1S5S7ReS4dS46GfA2A2S27G14G10A2M16A3S0S1S5S7ReS4dG4G12A2A2S27G15GdA2A3S0S1S5S7ReS4dS46G12A2A2S27G16GdA2A3S0ScS26S7RfR1A2S7RfS4aA2A2S1S5S7R10S45S16Sd8S4aR2A3A1A2S2bS29GdS7R10S4aA2A2S29GdS7R10R2A2A2A2A3F_;Fq;S1S5S7ReS4dG4G8A2A2S27G13G11A2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frho;").
Proof.
  intros rho H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13. zf H1. zf H2. zf H3. zf H4. zf H5. zf H6. zf H7. zf H8. zf H9. zf H10. zf H11. zf H12. zf H13.
  repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *. unfold B32 in *.
  rewrite uval_lit in H2, H3, H5, H6, H7, H8, H10, H11, H12, H13 by lia.
  pose proof (uval_range rho vQ) as RQ. pose proof (uval_range rho vK) as RK. pose proof (uval_range rho vKn) as RKn.
  pose proof (uval_range rho (SVar pN)) as RN. pose proof (uval_range rho vP) as RP. pose proof (uval_range rho (SVar 30)) as R30.
  assert (EQ : uval rho (kb16 vQ) = 16 * uval rho vQ) by (apply kb16_exact; unfold B32; lia).
  assert (EK : uval rho (kb16 vK) = 16 * uval rho vK) by (apply kb16_exact; unfold B32; lia).
  assert (EKn : uval rho (kb16 vKn) = 16 * uval rho vKn) by (apply kb16_exact; unfold B32; lia). rewrite EKn in H13.
  rewrite uval_add_small in H7 by (rewrite EKn; lia). rewrite EKn in H7.
  rewrite uval_add_small in H9 by (rewrite EK; lia). rewrite EK in H9.
  assert (E1 : uval rho q1 = uval rho vQ + 1) by (unfold q1; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; reflexivity).
  assert (E1k : uval rho (kb16 q1) = 16 * uval rho vQ + 16) by (rewrite kb16_exact by (unfold B32; lia); lia).
  repeat (split; [lia|]).
  split; [intros j Hj; unfold eoff; rewrite uval_add_small by (rewrite EQ, uval_lit by lia; lia); rewrite EQ, uval_lit by lia; reflexivity|].
  split; [exact E1|]. split; [exact E1k|].
  split.
  { unfold uval in *. rewrite U_add, U_sub, U_lit, EK, EQ. unfold M64v. rewrite Zplus_mod_idemp_l.
    change ((-16) mod 18446744073709551616) with 18446744073709551600.
    replace (16 * bv_unsigned (eval rho vK) - 16 * bv_unsigned (eval rho vQ) + 18446744073709551600) with ((16 * bv_unsigned (eval rho vK) - 16 * bv_unsigned (eval rho vQ) - 16) + 1 * 18446744073709551616) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  repeat (split; [lia|]).
  unfold pls. rewrite !uval_add_small by (rewrite ?EQ, ?E1k, ?EK; lia). rewrite EQ, E1k, EK.
  repeat (split; [lia|]). split; [|lia].
  intros q Hq. pose proof (uval_range rho q).
  assert (ES : uval rho (SAlu ALU_SUB vKn q) = uval rho vKn - uval rho q) by (unfold uval in *; rewrite U_sub; unfold M64v; apply Z.mod_small; lia).
  rewrite kb16_exact by (rewrite ES; unfold B32; lia). rewrite ES. lia.
Qed.

Ltac blocks HF :=
  let r := match type of HF with Forall (holds ?r) _ => r end in
  let H1 := fresh in let H2 := fresh in let H3 := fresh in let H4 := fresh in let H5 := fresh in let H6 := fresh in
  let H7 := fresh in let H8 := fresh in let H9 := fresh in let H10 := fresh in let H11 := fresh in let H12 := fresh in let H13 := fresh in
  fact HF (SPBranch BC_LTU vQ vK) H1; fact HF (SPUle vQ (SLit B32)) H2; fact HF (SPUle (SLit 1) vK) H3;
  fact HF (SPBranch BC_LTU vK vKn) H4; fact HF (SPUle vKn (SLit B32)) H5;
  fact HF (SPUle (SLit 4096) (SVar pN)) H6; fact HF (SPUle (SAlu ALU_ADD (SVar pN) (kb16 vKn)) (SLit 140737479966720)) H7;
  fact HF (SPUle (SLit 4096) vP) H8; fact HF (SPUle (SAlu ALU_ADD vP (kb16 vK)) (SVar 30)) H9; fact HF (SPUle (SVar 30) (SLit 140737479966720)) H10;
  fact HF (SPUle vP (SLit 140737488355328)) H11; fact HF (SPUle (SVar pN) (SLit 140737479966720)) H12; fact HF (SPUle (kb16 vKn) (SLit B32)) H13;
  destruct (blocks_arith _ H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13)
    as (?LqK & ?LKKn & ?LKn & ?LK1 & ?EQ16 & ?EK16 & ?EKn16 & ?Eoff & ?Eq1 & ?Eq1k & ?Erem & ?LN1 & ?LN2 & ?LP1 & ?LP2 & ?EdN & ?EdP & ?EdN1 & ?EdP1 & ?Efs & ?EdNK);
  clear H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13;
  pose proof (uval_range r vQ); pose proof (uval_range r vK); pose proof (uval_range r vKn); pose proof (uval_range r (SVar pN)); pose proof (uval_range r vP).

Lemma step_facts_ok : ltac2:(tb__ "0|0|
SbS9aS10SeR1A1SdS2cS64A1A1A3S9aS10SeR2A1S71A3F_;Frho;").
Proof.
  intros rho HF. blocks HF.
  fact HF (SPBranch BC_NE (SAlu ALU_ADD (SAlu ALU_SUB (kb16 vK) (kb16 vQ)) (SLit (-16))) (SLit 0)) HNE.
  apply (proj1 (holds_bne _ _ _)) in HNE. change (bv_unsigned (eval rho ?e) <> bv_unsigned (eval rho (SLit 0))) with (uval rho e <> uval rho (SLit 0)) in HNE.
  rewrite Erem, uval_lit in HNE by lia.
  unfold step_facts, fs_facts. constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
  - apply (proj2 (holds_bltu _ _ _)). change (uval rho q1 < uval rho vK). rewrite Eq1. lia.
  - apply (proj2 (h_ule _ _ _)). rewrite (Eoff 32), EK16 by lia. lia.
  - apply (proj2 (h_ule _ _ _)). rewrite (Eoff 32), EKn16 by lia. lia.
  - apply (proj2 (h_ule _ _ _)). rewrite uval_lit, (Efs q1) by lia. lia.
  - apply (proj2 (h_ule _ _ _)). rewrite uval_lit, (Efs q1) by (unfold B32; lia). unfold B32 in *. lia.
Qed.

Lemma cp0_facts_ok : ltac2:(tb__ "0|0|
SbS9aS10SeR1A1SdS2cS58A1A1A3S9aS10SeR2A1S79A3F_;Frho;").
Proof.
  intros rho HF.
  fact HF (SPUle (SLit 1) vK) H3. fact HF (SPBranch BC_LTU vK vKn) H4. fact HF (SPUle vKn (SLit B32)) H5. fact HF (SPUle (kb16 vKn) (SLit B32)) H6. zf H3. zf H4. zf H5. zf H6.
  repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *. unfold B32 in *. rewrite uval_lit in H3, H5, H6 by lia.
  pose proof (uval_range rho vK) as RK. pose proof (uval_range rho vKn) as RKn.
  assert (EK : uval rho (kb16 vK) = 16 * uval rho vK) by (apply kb16_exact; unfold B32; lia).
  assert (EKn : uval rho (kb16 vKn) = 16 * uval rho vKn) by (apply kb16_exact; unfold B32; lia). rewrite EKn in H6.
  assert (ES : uval rho (SAlu ALU_SUB vKn (SLit 0)) = uval rho vKn).
  { unfold uval in *. rewrite U_sub, U_lit. unfold M64v. change (0 mod 18446744073709551616) with 0. rewrite Z.sub_0_r. apply Z.mod_small. lia. }
  assert (EF : uval rho (kb16 (SAlu ALU_SUB vKn (SLit 0))) = 16 * uval rho vKn) by (rewrite kb16_exact by (rewrite ES; unfold B32; lia); lia).
  unfold cp0_facts, fs_facts. constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
  - apply (proj2 (holds_bltu _ _ _)). change (uval rho (SLit 0) < uval rho vK). rewrite uval_lit by lia. lia.
  - apply (proj2 (h_ule _ _ _)). rewrite EK, uval_lit by lia. lia.
  - apply (proj2 (h_ule _ _ _)). rewrite EKn, uval_lit by lia. lia.
  - apply (proj2 (h_ule _ _ _)). rewrite EF, uval_lit by lia. lia.
  - apply (proj2 (h_ule _ _ _)). rewrite EF, uval_lit by (unfold B32; lia). unfold B32 in *. lia.
Qed.

Lemma free_facts_ok : ltac2:(tb__ "0|0|
SbS9aS10SeR1A1SdS2cS60A1A1A3S9aS10SeR2A1S70A3F_;Frho;").
Proof.
  intros rho HF. blocks HF.
  fact HF (SPNot (SPBranch BC_NE (SAlu ALU_ADD (SAlu ALU_SUB (kb16 vK) (kb16 vQ)) (SLit (-16))) (SLit 0))) HEQ.
  apply (proj1 (holds_nbne _ _ _)) in HEQ. change (bv_unsigned (eval rho ?e) = bv_unsigned (eval rho (SLit 0))) with (uval rho e = uval rho (SLit 0)) in HEQ.
  rewrite Erem, uval_lit in HEQ by lia.
  unfold free_facts. constructor; [|constructor].
  apply (proj2 (h_ule _ _ _)). rewrite Eq1. lia.
Qed.

Lemma soff_u : ltac2:(tb__ "0|0|
SbScS28S7R2R1A2S2aZ2Z3fA2A2S1S5S25R3R2A2S7R3R2A2A3F_;Fe;Frho;").
Proof. intros rho e H. apply soff_smallu. exact H. Qed.

Lemma U_Z_to_bv : ltac2:(tb__ "0|1|
S5S0S26Z0R1A2S28R1S2aZ2Z40A2A2A2S1S5S43Q40M0S42G0R2A2A2R2A3F_;Fz;").
Proof. intros z Hz. apply u64_of_sum. exact Hz. Qed.

Lemma rd64_pair_bytes : ltac2:(tb__ "0|7|
S41Q40M0A1S38S41Q8A1A1M1F_;M2G2S5S5S5S5S1S38S5A1M3Sc3R6R4A2S3aS5R2A2M4A3S1G3Sc3R7S27R5Z8M5A2A2G4A3S1G3Sc3R7R5A2S3aS5R4A2M6A3S1G3Sc3R8S27R6G5A2A2G6A3S5S0S26Z0R1A2S28R1Z10A2A2S1G1RcS42G0S27RaR2A2A2A1RbS42G0S27R9R2A2A2A1A3F_;Fi;F_;F_;F_;F_;Fv1;Fv0;Fb;Fa;Fm2;Fm1;").
Proof.
  intros m1 m2 a b v0 v1 A0 A1 B0 B1 i Hi.
  destruct (Z_lt_dec i 8) as [L|L].
  - replace (a + i) with (a + Z.of_nat (Z.to_nat i)) by lia. replace (b + i) with (b + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (rd64_enc_bytes m1 a v0 A0) by lia. rewrite (rd64_enc_bytes m2 b v0 B0) by lia. reflexivity.
  - replace (a + i) with (a + 8 + Z.of_nat (Z.to_nat (i - 8))) by lia. replace (b + i) with (b + 8 + Z.of_nat (Z.to_nat (i - 8))) by lia.
    rewrite (rd64_enc_bytes m1 (a + 8) v1 A1) by lia. rewrite (rd64_enc_bytes m2 (b + 8) v1 B1) by lia. reflexivity.
Qed.

Definition Psi_fail (r0 rho : valuation) : Prop := ltac2:(tb__ "0|2|
S5S0S26S7Vr0;S46A2M0R1A2S28R1S27G0S29Z10S7Vr0;S44A2A2A2A2A2S1S38S41Q8A1A1S13Vrho;S42Q40R2A2M1A2S13Vr0;G1A2A3F_;Fz;").
Definition Psi_ok (r0 rho : valuation) : Prop := ltac2:(tb__ "0|8|
S0S5S0S26Z0R1A2M0S28R1S29Z10M1S7Vr0;S44A2A2A2A2S0S1S38S41Q8A1M2A1M3S13Vrho;S42Q40M4S27S7Vrho;S8cA2R2A2A2A2M5S13Vr0;S42G4S27S7Vr0;S46A2R2A2A2A2M6A3S2S1G3G6S3fG2A1M7A3A1A2F_;Fj;S5S0G0S28R1S29G1S7Vr0;S4aA2A2A2A2S2S1G3G5G7A3A1F_;Fj;A2").
Definition PDk_rr : list pdescK := ltac2:(tb__ "0|4|
S39S33S33S2dS91A2M0SbSbOFrho;Fr0;M1A2M2S35G0G1S35S2dS91S74S49S54S36S9A1M3A2A4Se0A4S39G2S35G0G1S35S2dS91S75S49S7dG3A2A4Se1A4S36G2A1A3A3").

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
Sb8SbS32S41Q40A1A1Sb9OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
SabS40VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S5SfaVCST;R1A2S0S26Z0R2A2S28R2Sf0A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S5SfaVXGL;R1A2S0S26Z0R2A2S28R2Sf0A2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S32S33S33S5S5A2S5A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 2 BX.
Variable rho0 : valuation.
Let HNP : NP_okA NF := NP_okA_intro NF eq_refl.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok.
Let P0 := P0_rr FB FF.

Definition Posts_rr : list (axst * jpostA) := ltac2:(tb__ "0|0|
SffVAInv;VCST;VXGL;VKc;S6aS92SdfVFB;VFF;VBX;Aa").

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S96VAInv;VCST;VXGL;S90VKc;Vrho0;VP0;VFB;VFF;VBX;S92Vnd;Ac").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
Sb1S40S90Vrho0;Vtp0;Sc9A5").

Definition ptr0 : Z := uval rho0 vP.
Definition K0 : Z := uval rho0 vK.
Definition Kn0 : Z := uval rho0 vKn.
Definition Phi0 (rho : valuation) : Prop := ltac2:(tb__ "0|1|
S5S0S26Sc6R1A2S28R1S27Sc6S29Z10ScaA2A2A2A2S1S38S41Q8A1A1S13Vrho;S42Q40R2A2M0A2S13Vrho0;G0A2A3F_;Fz;").
Definition Phi1 (rho : valuation) : Prop := ltac2:(tb__ "0|5|
S0Sc7Vrho;A1S0S5S0S26Z0R1A2S28R1S29Z10S7Vrho;S48A2A2M0A2A2S1S38S41Q8A1A1S13Vrho;S42Q40M1S27S7Vrho;S12S4cA1A2R2A2A2A2S13Vrho0;S42G1S27Sc6R2A2A2A2A3F_;Fj;S0S1S38S5A1M2Sc3S13Vrho;A1M3S27Sc6G0A2M4A2S3aS5S7Vrho;S8aA2A2A3S1G2Sc3G3S27G4Z8A2A2S3aS5S7Vrho;S8bA2A2A3A2A2A2").
Definition Phi2 (rho : valuation) : Prop := ltac2:(tb__ "0|6|
S0S5S0S26Z0R1A2M0S28R1S29Z10M1ScaA2A2A2S1S38S41Q8A1M2A1M3S13Vrho;S42Q40M4S27S7Vrho;S12S4cA1A2R2A2A2A2M5S13Vrho0;S42G4S27Sc6R2A2A2A2A3F_;Fj;S5S0G0S28R1S29G1ScbA2A2A2S2S1G3G5S3fG2A1A3A1F_;Fj;A2").
Definition Phis : list (list positive * (valuation -> Prop)) := ltac2:(tb__ "0|5|
S39S33S32S6A1M0SbOFrho;M1A2M2S35G0G1S36S6A1M3Sc7A4S39G2S35G0G1S39S6P6fM4S39S6PacS39S6PadS39S6PaeG3A3A3A3A3Sc5A4S39G2S35G0G1S39S6G4G3A3SccA4S36G2A1A3A3A3").
Let JAFv (k : nat) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
Se5VAInv;VCST;VXGL;S90VKc;Vrho0;VP0;VFB;VFF;VBX;S92Se9Sc8Vk;A2Vnd;Ad").

Lemma uval_rw : ltac2:(tb__ "0|1|
SbSbS6S1S41Q40A1S23R3R1A2S23R2R1A2A3S1S5S7R3S12R2A1M0A2S7R4G0A2A3F_;Fv;Frho';Frho;").
Proof. intros rho rho' v H. unfold uval. cbn [eval]. rewrite H. reflexivity. Qed.

Lemma Phis_reads : ltac2:(tb__ "0|3|
S9aS33S32S6A1M0SbOF_;M1A2M2G2SedS3bG0G1R1A3S3cG0G1R1A3A2Lp;Sc8A3").
Proof.
  unfold Phis. constructor; [|constructor; [|constructor; [|constructor]]]; cbn [fst snd]; unfold Phi2, Phi1, Phi0.
  - intros rho rho' _ _ HM H z Hz. rewrite <- HM. exact (H z Hz).
  - intros rho rho' HV _ HM (H0 & H1 & H2 & H3).
    assert (E111 : uval rho' (SVar pN) = uval rho (SVar pN)) by (apply uval_rw; apply HV; cbn; tauto).
    assert (E172 : uval rho' vQ = uval rho vQ) by (apply uval_rw; apply HV; cbn; tauto).
    assert (E173 : uval rho' vF0 = uval rho vF0) by (apply uval_rw; apply HV; cbn; tauto).
    assert (E174 : uval rho' vF1 = uval rho vF1) by (apply uval_rw; apply HV; cbn; tauto).
    rewrite E111, E172, E173, E174. split; [|split; [|split]].
    + intros z Hz. rewrite <- HM. exact (H0 z Hz).
    + intros j Hj. rewrite <- HM. exact (H1 j Hj).
    + rewrite (rd64_ext (rm rho) (rm rho')); [exact H2 | intros z _; symmetry; apply HM].
    + rewrite (rd64_ext (rm rho) (rm rho')); [exact H3 | intros z _; symmetry; apply HM].
  - intros rho rho' HV _ HM [H1 H2].
    assert (E111 : uval rho' (SVar pN) = uval rho (SVar pN)) by (apply uval_rw; apply HV; cbn; tauto).
    rewrite E111. split; intros j Hj; rewrite <- HM; [exact (H1 j Hj) | exact (H2 j Hj)].
Qed.

Lemma ejcertAF_ok : ltac2:(tb__ "0|0|
S1S31SebS40S90Sc8S80S86P64S7aS7bA8S34A3").
Proof. rewrite (ejcertAF_V segs NF Phis PhisV FUEL_rr cutpcs_rr 100 cutsE exitsE eq_refl). exact ejcertAF_ok0. Qed.

Lemma JA_P0 : ltac2:(tb__ "0|0|
S91S2dSbS32S41Q40A1A1SadS8dS40VJAv;R5A1R4R3R2R1A6S0VP0;Vrho0;A1Sc0S90Vrho0;R4A3A2F_;Fw;Ftp;Frho;FS;Fnd;").
Proof. intros nd S rho tp [tr [ms md]] [_ (Ai & kc & HJ)]. pose proof HJ as (Hav & _ & _ & _ & _ & _ & _ & _ & _ & HP0 & _). split; [exact HP0 | exact Hav]. Qed.

Lemma tracked_disjoint0 : ltac2:(tb__ "0|7|
Sb8SbS32S41Q40A1A1Sb9SbS32S33ScScA2M0A1S37S37G0G0VAInv;RaR9R8R7A4S99VFB;RbR7R6A4Sd2R8R7A2S1S38G0A1M1Sb6G0R8R7A3S3aG0R5A2M2A3S1G1Sb6G0R9R7A3G2A3S2S1S37R9R8A3A1ScdRcR8A2ScdRdR8A2S3S26S27S3bS5S5SceReRaA2M3A3M4S3cS5S5G3A3A2S3bS5S5SceReR9A2M5A3M6A2S26S27G6S3cS5S5G5A3A2G4A2A2F_;F_;F_;F_;F_;F_;F_;F_;Ftj;Fti;Fj;Fi;Ftv;Frho;Fm1;Ft1;Fr1;FAi;").
Proof.
  intros Ai r1 t1 m1 rho tv i j ti tj HM HN HD Hi Hj Hij Hzi Hzj.
  pose proof (tvd_nth rho _ i j ti tj HD Hi Hj Hij Hzi Hzj) as NE.
  destruct (proj1 (Forall_forall _ _) HN ti (nth_error_In _ _ Hi) Hzi) as (_ & Li & _).
  destruct (proj1 (Forall_forall _ _) HN tj (nth_error_In _ _ Hj) Hzj) as (_ & Lj & _).
  destruct (law_blocks' segs AInv CST ALA HCST Ai r1 t1 m1 HM) as (HPD & _ & _).
  apply In_nth_error in Li as [i1 Hi1]. apply In_nth_error in Lj as [i2 Hi2].
  destruct (Nat.eq_dec i1 i2) as [->|Hne12]; [exfalso; apply NE; rewrite Hi1 in Hi2; injection Hi2 as E1 E2; unfold tvv; rewrite E1, E2; reflexivity|].
  assert (Hi1' : nth_error (aa_live Ai ++ aa_frames Ai) i1 = Some (tvv rho ti)) by (rewrite nth_error_app1; [exact Hi1 | apply nth_error_Some; congruence]).
  assert (Hi2' : nth_error (aa_live Ai ++ aa_frames Ai) i2 = Some (tvv rho tj)) by (rewrite nth_error_app1; [exact Hi2 | apply nth_error_Some; congruence]).
  exact (pd_elems _ _ _ _ _ HPD Hi1' Hi2' Hne12).
Qed.
Lemma tracked_disjoint : ltac2:(tb__ "0|7|
S91SbS32S41Q40A1A1S32SbaA1Sb9S37S37S33ScScA2M0G0VJAv;R9R8R7R6R5A5S1S38G0A1M1Sb6G0S95RaA1R5A3S3aG0R3A2M2A3S1G1Sb6G0S95RbA1R5A3G2A3S2S1S37R7R6A3A1ScdRcR6A2ScdRdR6A2S3S26S27S3bS5S5SceReR8A2M3A3M4S3cS5S5G3A3A2S3bS5S5SceReR7A2M5A3M6A2S26S27G6S3cS5S5G5A3A2G4A2A2F_;F_;F_;F_;F_;F_;Ftj;Fti;Fj;Fi;Fmd;Ftr;Ftp;Frho;Fnd;").
Proof.
  intros nd rho tp tr md i j ti tj (Ai & kc & HJ) Hi Hj Hij Hzi Hzj.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & _).
  exact (tracked_disjoint0 Ai rho tp md rho _ i j ti tj HM HN HD Hi Hj Hij Hzi Hzj).
Qed.

Lemma al_extra_sound : ltac2:(tb__ "0|1|
SbS32SfA1S32S33ScScA2A1S32S33S33ScS5A2ScA2A1SfS5Sc0S90Vrho0;R6A3VP0;Vrho0;A1Sb5SfR4R7A3S1S31SdaR5A1S34A3S0S26S3bS5S5S1dRaR6A2M0A3R5A2S28R5S3cS5S5G0A3A2A2S3Sf9VCST;Vrho0;Sd0VFB;RbR9A3Sf8VFF;RbR8A3R6A5S3S0S26Z0R6A2S28R6Sf0A2A2Sf4R6A1A2A2F_;F_;F_;F_;F_;Fa;Fo;Ffr;Ftv';Fobjs;Frho;").
Proof.
  intros rho objs tv' fr o a Hav [(f & s & fl & Hin & H1 & H2) _] _ HE Hr. left.
  unfold extraAL in HE. apply lazy_andb_prop in HE as [Hb HE]. apply lazy_andb_prop in HE as [Hl Hh].
  apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh. unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Hb, Hl, Hh in Hr. cbn [fst snd] in Hr.
  rewrite !soff_lit_small in Hr by lia.
  assert (E12 : rw rho 12%positive = rw rho0 12%positive) by (symmetry; apply (proj1 Hav); reflexivity).
  unfold vA in Hr. cbn [eval] in Hr. rewrite E12 in Hr.
  right; right; right. exists f, s, fl. split; [apply In_FFx; left; exact Hin | lia].
Qed.

Lemma fs_extra_sound : ltac2:(tb__ "0|2|
SbScSfS5S26S7R4R3A2S7R4S4aA2A2S26S7R5S4aA2S4eA2S26Z1000S7R6S12S4cA1M0A2A2S26S27S7R7G0A2S29Z10S7R7S4aA2A2A2Z7fffff800000A2S1S31SdcR7R6A2S34A3S0S26S3bS5S5S1dR9R7A2M1A3R6A2S28R6S3cS5S5G1A3A2A2S3Sf9VCST;Vrho0;Sd0VFB;RaSd1S33ScScA2U1S47A3A3Sf8VFF;RaS36S33S33ScS5A2ScA2A1A3R7A5S3S0S26Z0R7A2S28R7Sf0A2A2Sf4R7A1A2A2F_;F_;F_;F_;F_;F_;Fa;Fo;Fc;Frho;").
Proof.
  intros rho c o a Hc HKn HN1 HN2 HE Hr. left. right; right; left.
  unfold extraFS in HE. apply lazy_andb_prop in HE as [Hb HE]. apply lazy_andb_prop in HE as [Hl Hh].
  apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
  pose proof (uval_range rho c) as Rc. pose proof (uval_range rho vKn) as RKn. unfold B32 in HKn.
  assert (Ec : uval rho (kb16 c) = 16 * uval rho c) by (apply kb16_exact; unfold B32; lia).
  assert (ES : uval rho (SAlu ALU_SUB vKn c) = uval rho vKn - uval rho c) by (unfold uval in *; rewrite U_sub; unfold M64v; apply Z.mod_small; lia).
  assert (Eh : uval rho (kb16 (SAlu ALU_SUB vKn c)) = 16 * uval rho vKn - 16 * uval rho c) by (rewrite kb16_exact by (rewrite ES; unfold B32; lia); lia).
  assert (EKn : uval rho (kb16 vKn) = 16 * uval rho vKn) by (apply kb16_exact; unfold B32; lia).
  assert (Eb : uval rho (SAlu ALU_ADD (SVar pN) (kb16 c)) = uval rho (SVar pN) + 16 * uval rho c) by (rewrite uval_add_small by (rewrite Ec; lia); lia).
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Hb, Hl, Hh in Hr. cbn [fst snd] in Hr.
  rewrite soff_lit_small in Hr by lia. rewrite (soff_u rho (kb16 (SAlu ALU_SUB vKn c))) in Hr by (rewrite Eh; lia).
  change (bv_unsigned (eval rho ?e)) with (uval rho e) in Hr. rewrite Eb, Eh in Hr.
  exists (uval rho (SVar pN)), (uval rho (kb16 vKn)). split; [|rewrite EKn; lia].
  apply In_FBx. right. exists (SVar pN, kb16 vKn). split; [left; reflexivity|]. split; [|reflexivity].
  unfold tnz. cbn [fst]. change (bv_unsigned (eval rho (SVar pN))) with (uval rho (SVar pN)). lia.
Qed.

Lemma agree_uval : ltac2:(tb__ "0|1|
S6SbSbS6S21R4R3R2A3SfbR2R5A2S1S5S7R4S12R3A1M0A2S7R5G0A2A3F_;F_;Fv;Frho';Frho;Fn;").
Proof. intros n rho rho' v (A & _ & _) Hv. unfold uval. cbn [eval]. rewrite <- (A v Hv). reflexivity. Qed.
Lemma agree_rm : ltac2:(tb__ "0|0|
S6SbSbS21R3R2R1A3S41Q40A1S1S38S41Q8A1A1S13R3R1A2S13R4R1A2A3Fa;F_;Frho';Frho;Fn;").
Proof. intros n rho rho' (_ & _ & C) a. symmetry. apply C. Qed.
Lemma vals_uval : ltac2:(tb__ "0|1|
SbS6Sc0S90Vrho0;R2A3SfbR2S90A2S1S5S7R4S12R3A1M0A2S7Vrho0;G0A2A3F_;F_;Fv;Frho;").
Proof. intros rho v Hav Hv. unfold uval. cbn [eval]. rewrite <- (proj1 Hav v Hv). reflexivity. Qed.

Lemma cp0_glue : ltac2:(tb__ "0|2|
SbS32S41Q40A1A1SadSc7R3A1S8dS40VJAv;S49S47S4bA2A1M0S58R4R3R2A6S4SbSbS0Sc5R1A1S0S1S5S7R1S44A2S7R6S44A2M1A3S0S1S5S7R1S48A2Z0A3S0S0S26Z1G1A2S26G1S4eA2A2S8dS40G0S5dR1R5R4A6A2A2A2A2Lr';A2F_;F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp [tr [ms md]] HPhi Hw.
  destruct (JA_P0 _ _ _ _ _ Hw) as [HP0 Hav]. pose proof (smatchA_facts segs _ _ _ _ (proj1 Hw)) as HF.
  pose proof chk_cp0 as (Cwf & Csite & Cnb & Cent & Cid & Ctv & Cnb2 & Cbud & Cfb).
  fact HF (SPUle (SLit 1) vK) H3. fact HF (SPBranch BC_LTU vK vKn) H4. fact HF (SPUle vKn (SLit B32)) H5. fact HF (SPUle vP (SLit 140737488355328)) H6.
  zf H3. zf H4. zf H5. zf H6. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *. unfold B32 in *. rewrite uval_lit in H3, H5, H6 by lia.
  pose proof (uval_range rho vK) as RK. pose proof (uval_range rho vP) as RP.
  assert (EK : uval rho (kb16 vK) = 16 * uval rho vK) by (apply kb16_exact; unfold B32; lia).
  assert (EB : uval rho (pls vP (kb16 (SLit 0))) = uval rho vP).
  { unfold pls, kb16. rewrite uval_add_small; rewrite uval_mul_lit, uval_lit by (rewrite ?uval_lit; lia); lia. }
  assert (EP : uval rho vP = ptr0) by (unfold ptr0; exact (vals_uval rho 13 Hav ltac:(reflexivity))).
  assert (EKK : uval rho vK = K0) by (unfold K0; exact (vals_uval rho 14 Hav ltac:(reflexivity))).

  assert (Hw1 : SPA segs (JAv (ndR tv1 bd1)) X_cp0f rho tp (tr, mkCfg ms md)).
  { unfold X_cp0f, ax_add_facts. apply (SPA_refacts_JA segs _ rho X_cp0 (cp0_facts ++ ss_facts (ax_S X_cp0))); [exact Hw | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
    intros tr' md' _ HF'. apply Forall_app. split; [exact (cp0_facts_ok rho HF') | exact HF']. }

  destruct (JA_carve_ent segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 P0 FB FF BX PTrue HKc HNP tv1 [] bd1 ANone 1 vP (kb16 vK)
              (pls vP (kb16 (SLit 0))) X_cp0f rho tp tr ms md eq_refl eq_refl Cwf ltac:(apply (proj1 (Pos.leb_le _ _)); reflexivity) Cnb)
    as (r1 & Hag & R0 & R1 & SP1).
  { intros r HFr. apply Forall_app in HFr as [_ HFr].
    fact HFr (SPUle (SLit 1) vK) Q3. fact HFr (SPBranch BC_LTU vK vKn) Q4. fact HFr (SPUle vKn (SLit B32)) Q5. fact HFr (SPUle vP (SLit 140737488355328)) Q6.
    zf Q3. zf Q4. zf Q5. zf Q6. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *. unfold B32 in *. rewrite uval_lit in Q3, Q5, Q6 by lia.
    pose proof (uval_range r vK). pose proof (uval_range r vP).
    assert (EKr : uval r (kb16 vK) = 16 * uval r vK) by (apply kb16_exact; unfold B32; lia).
    assert (EBr : uval r (pls vP (kb16 (SLit 0))) = uval r vP).
    { unfold pls, kb16. rewrite uval_add_small; rewrite uval_mul_lit, uval_lit by (rewrite ?uval_lit; lia); lia. }
    rewrite EBr, EKr. lia. }
  { apply (carve_site_chk_sound segs AInv CST ALA HCST NF rho0 P0 FB FF X_cp0f tv1 [] 1%nat extraAL rho Csite).
    intros Ai tp1 md1 _ HP0' Hav' _ _ _ _ _ _ _ _ _ o a Ho HE Hr. exact (al_extra_sound rho _ _ _ o a Hav' HP0' Ho HE Hr). }
  { intros z Hz. rewrite EB, EP in Hz. rewrite (HPhi z) by (unfold K0 in *; lia). apply (proj2 HP0). unfold ptr0, K0 in *. lia. }
  { exact Hw1. }
  rewrite (proj1 cp0_eqs) in SP1. change (ss_next (ax_S X_cp0f)) with 141%positive in Hag, R0, R1. change (Pos.succ 141) with 142%positive in R1.
  rewrite EB, EP in R0, R1.
  exists (rho_sub r1 s_cp0).
  assert (E14 : uval (rho_sub r1 s_cp0) vK = uval rho vK) by (etransitivity; [|exact (agree_uval _ rho r1 14 Hag ltac:(reflexivity))]; reflexivity).
  assert (E172 : uval (rho_sub r1 s_cp0) vQ = 0) by (etransitivity; [|exact (uval_lit r1 0 ltac:(lia))]; reflexivity).
  assert (E111 : uval (rho_sub r1 s_cp0) (SVar pN) = uval rho (SVar pN)) by (etransitivity; [|exact (agree_uval _ rho r1 pN Hag ltac:(reflexivity))]; reflexivity).
  assert (E173 : uval (rho_sub r1 s_cp0) vF0 = uval r1 (SVar 141)) by reflexivity.
  assert (E174 : uval (rho_sub r1 s_cp0) vF1 = uval r1 (SVar 142)) by reflexivity.
  assert (EM : rm (rho_sub r1 s_cp0) = rm r1) by reflexivity.
  split; [|split; [exact E14 | split; [exact E172 | split; [lia|]]]].
  - unfold Phi1, Phi0. rewrite E172, E111, E173, E174, EM. split; [|split; [|split]].
    + intros z Hz. rewrite (agree_rm _ _ _ Hag). exact (HPhi z Hz).
    + intros j Hj. lia.
    + rewrite Z.mul_0_r, Z.add_0_r. rewrite (rd64_ext (rm rho) (rm r1)) by (intros z _; apply (agree_rm _ _ _ Hag)). exact R0.
    + rewrite Z.mul_0_r, Z.add_0_r. rewrite (rd64_ext (rm rho) (rm r1)) by (intros z _; apply (agree_rm _ _ _ Hag)). exact R1.
  - apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc X_cp0c C_0 s_cp0 (ndR tv1 bd1) (ndR tv1 bd1) r1 tp _ Cent Cid);
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact Cnb2 | exact Ctv | reflexivity | exact Cbud | reflexivity | exact SP1].
Qed.

Lemma cont_lt : ltac2:(tb__ "0|0|
SbS9aS10SeR1A1SdS2cS53A1A1A3S28S27S7R2S48A2Z1A2S7R2S44A2A2F_;Frho;").
Proof.
  intros rho HF. blocks HF.
  fact HF (SPBranch BC_NE (SAlu ALU_ADD (SAlu ALU_SUB (kb16 vK) (kb16 vQ)) (SLit (-16))) (SLit 0)) HNE.
  apply (proj1 (holds_bne _ _ _)) in HNE. change (bv_unsigned (eval rho ?e) <> bv_unsigned (eval rho (SLit 0))) with (uval rho e <> uval rho (SLit 0)) in HNE.
  rewrite Erem, uval_lit in HNE by lia. lia.
Qed.
Lemma facts_X_p : ltac2:(tb__ "0|3|
S0S1S32S10A1M0SdS2cS59A1A1M1S3dS10S71SdS2cS53A1A1M2A3A3S0S1G0SdS2cS57A1A1G1A3S0S1G0SdS2cS4fA1A1G1A3S0S1G0SdS2cS5aA1A1G1A3S1G0SdS2cS64A1A1G2A3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma rng_dstX : ltac2:(tb__ "0|3|
SbS9aS10SeR1A1SdS2cS59A1A1A3S0S26S7R2S12S4cA1A2M0S7R2S18SdeA1A2M1A2S0S26S27G1S7R2S11Z10A1A2M2A2S27G0S7R2S45S4aA1A2A2A2S28Z0G2A2A2A2F_;Fr;").
Proof.
  intros r HFr. rewrite (proj1 facts_X_p) in HFr. apply Forall_app in HFr as [_ HF]. pose proof (cont_lt r HF) as HqK. blocks HF.
  cbn [ob_base o_dstX]. change (SAlu ALU_ADD (SVar 111) (SMd M_MUL (SLit 16) (SVar 172))) with (pls (SVar pN) (kb16 vQ)).
  rewrite EdN, EKn16, uval_lit by lia. lia.
Qed.
Lemma rng_srcX : ltac2:(tb__ "0|2|
SbS9aS10SeR1A1SdS2cS57A1A1A3S0S26S7R2S46A2M0S7R2S18SdbS48A1A1A2M1A2S26S27G1Z10A2S27G0S7R2S45S44A1A2A2A2A2F_;Fr;").
Proof.
  intros r HFr. rewrite (proj1 (proj2 facts_X_p)), (proj1 facts_X_p) in HFr. apply Forall_app in HFr as [_ HF]. blocks HF.
  cbn [ob_base o_src ent_obj]. rewrite EdP, EK16. lia.
Qed.
Lemma rng_nxtX : ltac2:(tb__ "0|2|
SbS9aS10SeR1A1SdS2cS4fA1A1A3S0S26S7R2S46A2M0S7R2S4dS46S45S50A1A2A2M1A2S26S27G1Z10A2S27G0S7R2S45S44A1A2A2A2A2F_;Fr;").
Proof.
  intros r HFr. rewrite (proj1 (proj2 (proj2 facts_X_p))), (proj1 facts_X_p) in HFr. apply Forall_app in HFr as [_ HF]. pose proof (cont_lt r HF) as HqK. blocks HF.
  rewrite EdP1, EK16. lia.
Qed.
Lemma fs_boundsX : ltac2:(tb__ "0|2|
SbS9aS10SeR1A1SdS2cS4fA1A1A3S0S26S7R2S50A2S7R2S4aA2M0A2S0S26G0S4eA2S0S26Z1000S7R2S12S4cA1A2M1A2S26S27G1S29Z10G0A2A2Z7fffff800000A2A2A2A2F_;Fr;").
Proof.
  intros r HFr. rewrite (proj1 (proj2 (proj2 facts_X_p))), (proj1 facts_X_p) in HFr. apply Forall_app in HFr as [_ HF]. pose proof (cont_lt r HF) as HqK. blocks HF.
  rewrite Eq1. unfold B32 in *. lia.
Qed.

Lemma step_glue : ltac2:(tb__ "0|3|
SbS32S41Q40A1A1SadSc5R3A1S8dS40VJAv;S49S47S4bA2A1M0S53R4R3R2A6S4SbSbS0Sc5R1A1S0S1S5S7R1S44A2S7R6S44A2M1A3S0S1S5S7R1S48A2S27S7R6S48A2Z1A2M2A3S0S28G2G1A2S0S26G1S4eA2S8dS40G0S5dR1R5R4A6A2A2A2A2A2Lr';A2F_;F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp [tr [ms md]] (HP0i & HPc & HR0 & HR1) Hw.
  destruct (JA_P0 _ _ _ _ _ Hw) as [HP0 Hav]. pose proof (smatchA_facts segs _ _ _ _ (proj1 Hw)) as HF.
  pose proof chk_X as (Cwf & Csite & Cnb & Cent & Cid & Ctv & Cnb2 & Cbud & Cwf2 & Cfb).
  pose proof X_eqs as (Xt & Xs & Xn2 & Xr & Xp & Xo1 & Xd1 & Xo2 & Xd2 & Xc).
  pose proof facts_X_p as (Fp & Fa1 & Fa2 & Fs & Ft).
  pose proof (cont_lt rho HF) as HqK. blocks HF.
  assert (EP : uval rho vP = ptr0) by (unfold ptr0; exact (vals_uval rho 13 Hav ltac:(reflexivity))).
  assert (EKK : uval rho vK = K0) by (unfold K0; exact (vals_uval rho 14 Hav ltac:(reflexivity))).

  pose proof (SPA_tiles segs (JAv (ndR tv1 bd1)) rho tiles2 X_step (ax_S X_t) tp _ Xt Hw) as Hw1. change (ax_setS X_step (ax_S X_t)) with X_t in Hw1.
  assert (Hw2 : SPA segs (JAv (ndR tv1 bd1)) X_f rho tp (tr, mkCfg ms md)).
  { unfold X_f, ax_add_facts. apply (SPA_refacts_JA segs _ rho X_t (step_facts ++ ss_facts (ax_S X_t))); [exact Hw1 | exact Cfb |].
    intros tr' md' _ HF'. apply Forall_app. split; [exact (step_facts_ok rho HF') | exact HF']. }
  pose proof (SPA_axforms segs (JAv (ndR tv1 bd1)) [AXSplit 1 (SLit 16)] rho X_f X_s tp _ Xs Hw2) as Hw3.
  assert (Hw4 : SPA segs (JAv (ndR tv1 bd1)) X_r rho tp (tr, mkCfg ms md)).
  { rewrite <- Xr. apply (SPA_reshape segs _ rho X_s 2 o_restX (O_fs (SVar pN) q1 vKn) tp _ Xn2); [reflexivity | reflexivity | reflexivity | exact Cwf2 | | exact Hw3].
    intros _. unfold obj_lo_of, obj_hi_of, O_fs, o_restX. cbn [ob_base ob_lo ob_hi].
    change (SMd M_MUL (SLit 16) (SAlu ALU_SUB (SVar 33) (SVar 172))) with (kb16 (SAlu ALU_SUB vKn vQ)).
    change (SAlu ALU_ADD (SVar 111) (SMd M_MUL (SLit 16) (SVar 172))) with (pls (SVar pN) (kb16 vQ)).
    change (SAlu ALU_ADD (SVar pN) (kb16 q1)) with (pls (SVar pN) (kb16 q1)).
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e). rewrite !soff_lit_small by lia.
    rewrite (soff_u rho (kb16 (SAlu ALU_SUB vKn q1))) by (rewrite Efs by lia; lia). rewrite (soff_u rho (kb16 (SAlu ALU_SUB vKn vQ))) by (rewrite Efs by lia; lia).
    rewrite !Efs by lia. rewrite EdN1, EdN, Eq1. lia. }
  pose proof (SPA_axforms segs (JAv (ndR tv1 bd1)) [AXSelect sel8] rho X_r X_p tp _ Xp Hw4) as Hw5.

  assert (NZ1 : tnz rho (SVar pN, kb16 vKn)) by (unfold tnz; cbn [fst]; change (bv_unsigned (eval rho (SVar pN))) with (uval rho (SVar pN)); lia).
  assert (NZ2 : tnz rho (vP, kb16 vK)) by (unfold tnz; cbn [fst]; change (bv_unsigned (eval rho vP)) with (uval rho vP); lia).
  assert (DISJ : uval rho (SVar pN) + 16 * uval rho vKn <= uval rho vP \/ uval rho vP + 16 * uval rho vK <= uval rho (SVar pN)).
  { destruct Hw5 as [_ HJ]. cbn [w_tr w_cfg cfg_model snd fst] in HJ.
    pose proof (tracked_disjoint (ndR tv1 bd1) rho tp tr md 0 1 (SVar pN, kb16 vKn) (vP, kb16 vK) HJ eq_refl eq_refl ltac:(lia) NZ1 NZ2) as D.
    unfold tvv in D. cbn [fst snd] in D. repeat change (bv_unsigned (eval rho ?e)) with (uval rho e) in D. rewrite EKn16, EK16 in D. exact D. }

  destruct (JA_absorb_tr segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 P0 FB FF BX PTrue tv1 [] bd1 ANone 0 (SVar pN) (kb16 vKn)
              X_p (ss_objs (ax_S X_a1)) o_dstX (SLit 16) rho tp tr ms md Xo1 eq_refl eq_refl eq_refl eq_refl rng_dstX Hw5) as (Hw6 & OUT2 & DEF2 & CELLS2).
  rewrite Xd1 in Hw6. cbn [ob_base o_dstX] in OUT2, DEF2, CELLS2.
  change (SAlu ALU_ADD (SVar 111) (SMd M_MUL (SLit 16) (SVar 172))) with (pls (SVar pN) (kb16 vQ)) in OUT2, DEF2, CELLS2.
  rewrite EdN, (uval_lit rho 16) in OUT2, DEF2, CELLS2 by lia.
  set (rho2 := rho_absorb rho [o_dstX] (vms md tp ms)) in *.
  assert (UV2 : forall e, uval rho2 e = uval rho e) by (intros e; unfold uval, rho2; rewrite eval_absorb; reflexivity).
  assert (OLD2 : forall z, uval rho vP <= z < uval rho vP + 16 * uval rho vK -> rm rho2 (Z_to_bv 64 z) = rm rho (Z_to_bv 64 z)).
  { intros z Hz. apply OUT2. rewrite U_Z_to_bv by lia. lia. }
  pose proof (CELLS2 0 vF0 ltac:(cbn; tauto) ltac:(lia) ltac:(lia)) as C0. rewrite Z.add_0_r in C0. change (uval rho vF0) with (uval rho vF0) in C0.
  pose proof (CELLS2 8 vF1 ltac:(cbn; tauto) ltac:(lia) ltac:(lia)) as C1.

  destruct (JA_absorb_ent_same segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 P0 FB FF BX PTrue tv1 [] bd1 ANone 1 vP (kb16 vK)
              X_a1 (ss_objs (ax_S X_a2)) (o_src vQ) vF0 vF1 rho2 tp tr ms md Xo2 eq_refl eq_refl eq_refl eq_refl ltac:(cbn; tauto) ltac:(cbn; tauto) rng_srcX) as [Hw7 RM3].
  { cbn [ob_base o_src ent_obj]. rewrite !UV2, EdP. rewrite (rd64_ext (rm rho) (rm rho2)) by (intros z Hz; apply OLD2; lia). rewrite EP. exact HR0. }
  { cbn [ob_base o_src ent_obj]. rewrite !UV2, EdP. rewrite (rd64_ext (rm rho) (rm rho2)) by (intros z Hz; apply OLD2; lia). rewrite EP. exact HR1. }
  { exact Hw6. }
  rewrite Xd2 in Hw7. set (rho3 := rho_absorb rho2 [o_src vQ] (vms md tp ms)) in *.
  assert (UV3 : forall e, uval rho3 e = uval rho e) by (intros e; etransitivity; [|apply UV2]; unfold uval, rho3; rewrite eval_absorb; reflexivity).

  destruct (JA_carve_ent segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 P0 FB FF BX PTrue HKc HNP tv1 [] bd1 ANone 1 vP (kb16 vK)
              (pls vP (kb16 q1)) X_a2 rho3 tp tr ms md eq_refl eq_refl Cwf ltac:(apply (proj1 (Pos.leb_le _ _)); reflexivity) Cnb)
    as (r4 & Hag & Q0 & Q1 & SP4).
  { exact rng_nxtX. }
  { apply (carve_site_chk_sound segs AInv CST ALA HCST NF rho0 P0 FB FF X_a2 tv1 [] 1%nat extraX rho3 Csite).
    intros Ai tp1 md1 HFa HP0' Hav' _ _ _ _ _ _ _ _ _ o a Ho HE Hr. unfold extraX in HE. apply lazy_orb_prop in HE as [HE|HE].
    - exact (al_extra_sound rho3 _ _ _ o a Hav' HP0' Ho HE Hr).
    - destruct (fs_boundsX rho3 HFa) as (B1 & B2 & B3 & B4). exact (fs_extra_sound rho3 q1 o a B1 B2 B3 B4 HE Hr). }
  { intros z Hz. rewrite UV3, EdP1 in Hz. unfold rho3. rewrite RM3. rewrite OLD2 by lia. rewrite EP, EKK in *. rewrite (HP0i z) by lia. apply (proj2 HP0). unfold ptr0, K0 in *. lia. }
  { exact Hw7. }
  rewrite Xc in SP4. change (ss_next (ax_S X_a2)) with 179%positive in Hag, Q0, Q1. change (Pos.succ 179) with 180%positive in Q1.
  rewrite UV3, EdP1, EP in Q0, Q1.
  assert (RM4 : forall a, rm r4 a = rm rho3 a) by (apply (agree_rm _ _ _ Hag)).
  exists (rho_sub r4 s_step).
  assert (E14 : uval (rho_sub r4 s_step) vK = uval rho vK).
  { etransitivity; [|apply UV3]. etransitivity; [|exact (agree_uval _ rho3 r4 14 Hag ltac:(reflexivity))]. reflexivity. }
  assert (E172 : uval (rho_sub r4 s_step) vQ = uval rho vQ + 1).
  { rewrite <- Eq1, <- (UV3 q1). transitivity (uval r4 q1); [reflexivity|]. unfold uval. rewrite <- (eval_agree 179 rho3 r4 q1 Hag eq_refl). reflexivity. }
  assert (E111 : uval (rho_sub r4 s_step) (SVar pN) = uval rho (SVar pN)).
  { etransitivity; [|apply UV3]. etransitivity; [|exact (agree_uval _ rho3 r4 pN Hag ltac:(reflexivity))]. reflexivity. }
  assert (E173 : uval (rho_sub r4 s_step) vF0 = uval r4 (SVar 179)) by reflexivity.
  assert (E174 : uval (rho_sub r4 s_step) vF1 = uval r4 (SVar 180)) by reflexivity.
  assert (EM : rm (rho_sub r4 s_step) = rm r4) by reflexivity.
  split; [|split; [exact E14 | split; [exact E172 | split; [lia | split; [unfold B32 in *; lia|]]]]].
  - unfold Phi1, Phi0. rewrite E172, E111, E173, E174, EM. split; [|split; [|split]].
    + intros z Hz. rewrite RM4. unfold rho3. rewrite RM3. rewrite OLD2 by (rewrite EP, EKK; lia). exact (HP0i z Hz).
    + intros j Hj. rewrite RM4. unfold rho3. rewrite RM3.
      destruct (Z_lt_dec j (16 * uval rho vQ)) as [L|L].
      * rewrite OUT2 by (rewrite U_Z_to_bv by lia; lia). apply HPc. lia.
      * replace (uval rho (SVar pN) + j) with (uval rho (SVar pN) + 16 * uval rho vQ + (j - 16 * uval rho vQ)) by lia.
        rewrite (rd64_pair_bytes (rm rho2) (rm rho) _ _ (uval rho vF0) (uval rho vF1) C0 C1 HR0 HR1 (j - 16 * uval rho vQ)) by lia.
        replace (ptr0 + 16 * uval rho vQ + (j - 16 * uval rho vQ)) with (ptr0 + j) by lia. apply HP0i. rewrite <- EKK. lia.
    + rewrite (rd64_ext (rm rho3) (rm r4)) by (intros z _; apply RM4). replace (ptr0 + 16 * (uval rho vQ + 1)) with (ptr0 + 16 * uval rho vQ + 16) by lia. exact Q0.
    + rewrite (rd64_ext (rm rho3) (rm r4)) by (intros z _; apply RM4). replace (ptr0 + 16 * (uval rho vQ + 1) + 8) with (ptr0 + 16 * uval rho vQ + 16 + 8) by lia. exact Q1.
  - apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc X_c C_0 s_step (ndR tv1 bd1) (ndR tv1 bd1) r4 tp _ Cent Cid);
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact Cnb2 | exact Ctv | reflexivity | exact Cbud | reflexivity | exact SP4].
Qed.

Lemma facts_E_p : ltac2:(tb__ "0|3|
S0S1S32S10A1M0SdS2cS52A1A1M1S3dS10S70SdS2cS5fA1A1M2A3A3S0S1G0SdS2cS55A1A1G1A3S0S1G0SdS2cS51A1A1G1A3S0S1G0SdS2cS60A1A1G2A3S0S1G0SdS2cS5eA1A1G1A3S1G0SdS2cS56A1A1G1A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma lastK : ltac2:(tb__ "0|0|
SbS9aS10SeR1A1SdS2cS52A1A1A3S1S5S7R2S44A2S27S7R2S48A2Z1A2A3F_;Fr;").
Proof.
  intros r HFr. rewrite (proj1 facts_E_p) in HFr. apply Forall_app in HFr as [H1 HF]. blocks HF.
  apply Forall_inv in H1. zf H1. rewrite Eq1 in H1. lia.
Qed.
Lemma rng_dstE : ltac2:(tb__ "0|3|
SbS9aS10SeR1A1SdS2cS52A1A1A3S0S26S7R2S12S4cA1A2M0S7R2S18SddA1A2M1A2S0S26S27G1S7R2S45S16Sd8S4aS48A3A1A2M2A2S27G0S7R2S45S4aA1A2A2A2S28Z0G2A2A2A2F_;Fr;").
Proof.
  intros r HFr. rewrite (proj1 facts_E_p) in HFr. apply Forall_app in HFr as [_ HF]. blocks HF.
  cbn [ob_base o_dstE]. change (SAlu ALU_ADD (SVar 111) (SMd M_MUL (SLit 16) (SVar 172))) with (pls (SVar pN) (kb16 vQ)).
  rewrite EdN, EKn16, Efs by lia. lia.
Qed.
Lemma rng_srcE : ltac2:(tb__ "0|2|
SbS9aS10SeR1A1SdS2cS55A1A1A3S0S26S7R2S46A2M0S7R2S18SdbS48A1A1A2M1A2S26S27G1Z10A2S27G0S7R2S45S44A1A2A2A2A2F_;Fr;").
Proof.
  intros r HFr. rewrite (proj1 (proj2 facts_E_p)), (proj1 facts_E_p) in HFr. apply Forall_app in HFr as [_ HF]. blocks HF.
  cbn [ob_base o_src ent_obj]. rewrite EdP, EK16. lia.
Qed.
Lemma rng_oldE : ltac2:(tb__ "0|3|
SbS9aS10SeR1A1SdS2cS51A1A1A3S0S26S7R2S46A2M0G0A2S0S26S27G0S7R2S45S44A1A2M1A2M2G2A2S28Z0G1A2A2A2F_;Fr;").
Proof.
  intros r HFr. rewrite (proj1 (proj2 (proj2 facts_E_p))), (proj1 facts_E_p) in HFr. apply Forall_app in HFr as [_ HF]. blocks HF. rewrite EK16. lia.
Qed.

Lemma free_glue : ltac2:(tb__ "0|1|
SbS32S41Q40A1A1SadSc5R3A1S8dS40VJAv;S49S47S4bA2A1M0S5fR4R3R2A6S4SbSbS0SccR1A1S0S2S1S5S7R1S12S4cA1A2Z0A3A1S0S1S5S7R1S45S4aA1A2S29Z10ScbA2A3S0S28ScaScbA2S8dS40G0S56R1R5R4A6A2A2A2A2Lr';A2F_;F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp [tr [ms md]] (HP0i & HPc & HR0 & HR1) Hw.
  destruct (JA_P0 _ _ _ _ _ Hw) as [HP0 Hav]. pose proof (smatchA_facts segs _ _ _ _ (proj1 Hw)) as HF.
  pose proof chk_E as (Cwf & Csite & Cent & Ctv & Cnb2 & Cbud & Cfb).
  pose proof E_eqs as (Xt & Xp & Xo1 & Xd1 & Xo2 & Xd2 & Xc).
  pose proof facts_E_p as (Fp & Fa1 & Fa2 & Ft & Fc & FT).
  blocks HF.
  assert (EP : uval rho vP = ptr0) by (unfold ptr0; exact (vals_uval rho 13 Hav ltac:(reflexivity))).
  assert (EKK : uval rho vK = K0) by (unfold K0; exact (vals_uval rho 14 Hav ltac:(reflexivity))).
  assert (EKN : uval rho vKn = Kn0) by (unfold Kn0; exact (vals_uval rho 33 Hav ltac:(reflexivity))).

  pose proof (SPA_tiles segs (JAv (ndR tv1 bd1)) rho tiles2 E_free (ax_S E_ft) tp _ Xt Hw) as Hw1. change (ax_setS E_free (ax_S E_ft)) with E_ft in Hw1.
  assert (Hw2 : SPA segs (JAv (ndR tv1 bd1)) E_ff rho tp (tr, mkCfg ms md)).
  { unfold E_ff, ax_add_facts. apply (SPA_refacts_JA segs _ rho E_ft (free_facts ++ ss_facts (ax_S E_ft))); [exact Hw1 | exact Cfb |].
    intros tr' md' _ HF'. apply Forall_app. split; [exact (free_facts_ok rho HF') | exact HF']. }
  pose proof (SPA_axforms segs (JAv (ndR tv1 bd1)) [AXSelect sel7] rho E_ff E_fp tp _ Xp Hw2) as Hw5.
  pose proof (smatchA_facts segs _ _ _ _ (proj1 Hw5)) as HF5. pose proof (lastK rho HF5) as HK.

  assert (NZ1 : tnz rho (SVar pN, kb16 vKn)) by (unfold tnz; cbn [fst]; change (bv_unsigned (eval rho (SVar pN))) with (uval rho (SVar pN)); lia).
  assert (NZ2 : tnz rho (vP, kb16 vK)) by (unfold tnz; cbn [fst]; change (bv_unsigned (eval rho vP)) with (uval rho vP); lia).
  assert (DISJ : uval rho (SVar pN) + 16 * uval rho vKn <= uval rho vP \/ uval rho vP + 16 * uval rho vK <= uval rho (SVar pN)).
  { destruct Hw5 as [_ HJ]. cbn [w_tr w_cfg cfg_model snd fst] in HJ.
    pose proof (tracked_disjoint (ndR tv1 bd1) rho tp tr md 0 1 (SVar pN, kb16 vKn) (vP, kb16 vK) HJ eq_refl eq_refl ltac:(lia) NZ1 NZ2) as D.
    unfold tvv in D. cbn [fst snd] in D. repeat change (bv_unsigned (eval rho ?e)) with (uval rho e) in D. rewrite EKn16, EK16 in D. exact D. }

  destruct (JA_absorb_tr segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 P0 FB FF BX PTrue tv1 [] bd1 ANone 0 (SVar pN) (kb16 vKn)
              E_fp (ss_objs (ax_S E_fa1)) o_dstE (kb16 (SAlu ALU_SUB vKn vQ)) rho tp tr ms md Xo1 eq_refl eq_refl eq_refl eq_refl rng_dstE Hw5) as (Hw6 & OUT2 & DEF2 & CELLS2).
  rewrite Xd1 in Hw6. cbn [ob_base o_dstE] in OUT2, DEF2, CELLS2.
  change (SAlu ALU_ADD (SVar 111) (SMd M_MUL (SLit 16) (SVar 172))) with (pls (SVar pN) (kb16 vQ)) in OUT2, DEF2, CELLS2.
  rewrite EdN, (Efs vQ) in OUT2, DEF2, CELLS2 by lia.
  set (rho2 := rho_absorb rho [o_dstE] (vms md tp ms)) in *.
  assert (UV2 : forall e, uval rho2 e = uval rho e) by (intros e; unfold uval, rho2; rewrite eval_absorb; reflexivity).
  assert (OLD2 : forall z, uval rho vP <= z < uval rho vP + 16 * uval rho vK -> rm rho2 (Z_to_bv 64 z) = rm rho (Z_to_bv 64 z)).
  { intros z Hz. apply OUT2. rewrite U_Z_to_bv by lia. lia. }
  pose proof (CELLS2 0 vF0 ltac:(cbn; tauto) ltac:(lia) ltac:(lia)) as C0. rewrite Z.add_0_r in C0.
  pose proof (CELLS2 8 vF1 ltac:(cbn; tauto) ltac:(lia) ltac:(lia)) as C1.

  destruct (JA_absorb_ent_same segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 P0 FB FF BX PTrue tv1 [] bd1 ANone 1 vP (kb16 vK)
              E_fa1 (ss_objs (ax_S E_fa2)) (o_src vQ) vF0 vF1 rho2 tp tr ms md Xo2 eq_refl eq_refl eq_refl eq_refl ltac:(cbn; tauto) ltac:(cbn; tauto) rng_srcE) as [Hw7 RM3].
  { cbn [ob_base o_src ent_obj]. rewrite !UV2, EdP. rewrite (rd64_ext (rm rho) (rm rho2)) by (intros z Hz; apply OLD2; lia). rewrite EP. exact HR0. }
  { cbn [ob_base o_src ent_obj]. rewrite !UV2, EdP. rewrite (rd64_ext (rm rho) (rm rho2)) by (intros z Hz; apply OLD2; lia). rewrite EP. exact HR1. }
  { exact Hw6. }
  rewrite Xd2 in Hw7. set (rho3 := rho_absorb rho2 [o_src vQ] (vms md tp ms)) in *.
  assert (UV3 : forall e, uval rho3 e = uval rho e) by (intros e; etransitivity; [|apply UV2]; unfold uval, rho3; rewrite eval_absorb; reflexivity).

  destruct (JA_carve_tr segs AInv CST XGL ALA HCST HXGL NF Kc rho0 P0 FB FF BX PTrue HNP tv1 [] bd1 ANone 1 vP (kb16 vK) vP (kb16 vK)
              E_fa2 rho3 tp tr ms md eq_refl eq_refl Cwf rng_oldE) as (Hw8 & _ & _ & _).
  { apply (carve_site_chk_sound segs AInv CST ALA HCST NF rho0 P0 FB FF E_fa2 tv1 [] 1%nat extraAL rho3 Csite).
    intros Ai tp1 md1 HFa HP0' Hav' _ _ _ _ _ _ _ _ _ o a Ho HE Hr. exact (al_extra_sound rho3 _ _ _ o a Hav' HP0' Ho HE Hr). }
  { intros z Hz. rewrite !UV3, EK16 in Hz. unfold rho3. rewrite RM3. rewrite OLD2 by lia. rewrite EP, EKK in *. rewrite (HP0i z) by lia. apply (proj2 HP0). unfold ptr0, K0 in *. lia. }
  { exact Hw7. }
  rewrite Xc in Hw8.
  exists (rho_sub rho3 []).
  assert (E111 : uval (rho_sub rho3 []) (SVar pN) = uval rho (SVar pN)) by (etransitivity; [|apply UV3]; reflexivity).
  assert (EKn4 : uval (rho_sub rho3 []) (kb16 vKn) = uval rho (kb16 vKn)) by (etransitivity; [|apply UV3]; reflexivity).
  assert (EM : rm (rho_sub rho3 []) = rm rho3) by reflexivity.
  split; [|split; [rewrite E111; lia | split; [rewrite EKn4, EKn16, <- EKN; lia| split; [rewrite <- EKK, <- EKN; lia|]]]].
  - unfold Phi2. rewrite E111, EM. unfold rho3. split.
    + intros j Hj. rewrite RM3.
      destruct (Z_lt_dec j (16 * uval rho vQ)) as [L|L].
      * rewrite OUT2 by (rewrite U_Z_to_bv by lia; lia). apply HPc. lia.
      * replace (uval rho (SVar pN) + j) with (uval rho (SVar pN) + 16 * uval rho vQ + (j - 16 * uval rho vQ)) by lia.
        rewrite (rd64_pair_bytes (rm rho2) (rm rho) _ _ (uval rho vF0) (uval rho vF1) C0 C1 HR0 HR1 (j - 16 * uval rho vQ)) by (rewrite <- EKK in Hj; lia).
        replace (ptr0 + 16 * uval rho vQ + (j - 16 * uval rho vQ)) with (ptr0 + j) by lia. apply HP0i. lia.
    + intros j Hj. rewrite RM3.
      destruct (Z_lt_dec j (16 * uval rho vQ)) as [L|L].
      * rewrite OUT2 by (rewrite U_Z_to_bv by lia; lia). rewrite (HPc j) by lia. apply (proj2 HP0). unfold ptr0, K0, Kn0 in *. lia.
      * apply DEF2. lia.
  - apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc E_fc E_freeT [] (ndR tv1 bd1) (ndR tv1 bd1) rho3 tp _ Cent eq_refl);
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact Cnb2 | exact Ctv | reflexivity | exact Cbud | reflexivity | exact Hw8].
Qed.

Lemma Phi0_keptR : ltac2:(tb__ "0|3|
S32S33ScScA2M0A1SbSbSb5G0S35ScScS46S45S44A1M1A4R3A3Sc0S90Vrho0;R3A3S2S1S5S7R4S46A2Z0A3A1S1S5S7R5G1A2S29Z10S7R5S44A2A2A3S100R6R7R5A3Sc7R7A1M2G2F_;F_;F_;F_;F_;F_;Frho';Frho;Ftv;").
Proof.
  intros tv rho rho' Hin Hav Hnz EK HK H z Hz.
  assert (EP : uval rho vP = ptr0) by (unfold ptr0; exact (vals_uval rho 13 Hav ltac:(reflexivity))).
  assert (EKK : uval rho vK = K0) by (unfold K0; exact (vals_uval rho 14 Hav ltac:(reflexivity))).
  rewrite (HK (vP, kb16 vK) z Hin); [exact (H z Hz) | unfold tnz; cbn [fst]; exact Hnz |].
  unfold tvv. cbn [fst snd]. repeat change (bv_unsigned (eval rho ?e)) with (uval rho e). rewrite EK, EP, EKK. exact Hz.
Qed.

Lemma P0_frame : ltac2:(tb__ "0|1|
Sb8SbSc0S90Vrho0;R1A3VP0;Vrho0;A1S97VFF;R4A2S38S5A1S5S0S26S43Q40S22R6S69A2A2M0R1A2S28R1S27G0Z30A2A2A2Sf6VCST;R8R3R2A4F_;Fa;Fx;F_;F_;F_;Frho;FAi;").
Proof.
  intros Ai rho Hav [(f & sz & fl & Hin & H1 & H2) _] HFF x a Ha.
  assert (E12 : rw rho 12%positive = rw rho0 12%positive) by (symmetry; apply (proj1 Hav); reflexivity).
  unfold vA in Ha. cbn [eval] in Ha. rewrite E12 in Ha.
  right; right; right. exists f, sz. split; [exact (proj1 (HFF _ _ _ Hin)) | lia].
Qed.
Lemma al_obj_range : ltac2:(tb__ "0|3|
SbSfS5S1S31S19S18R2A1S69A2S34A3S1ScS1cR3A1S11Z0A1A3S1ScS1bR4A1S11Z30M0A1A3S0S26S3bS5S5S1dR6R5A2M1A3R4A2S28R4S3cS5S5G1A3A2A2S0S26S43Q40S22R7S69A2A2M2R5A2S28R5S27G2G0A2A2A2F_;F_;F_;F_;Fa;Fo;Frho;").
Proof.
  intros rho o a Hb Hl Hh Hr. apply sv_eqb_sound in Hb. unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Hb, Hl, Hh in Hr.
  cbn [fst snd] in Hr. rewrite !soff_lit_small in Hr by lia. lia.
Qed.

Lemma site_m : ltac2:(tb__ "0|1|
SbSf5VAInv;VCST;VXGL;S90Vrho0;VP0;VFB;VFF;S61S5cS62R1S49S54S65A2S3fS5A1Sb8Sc4S0S0S26Z1S7R3SbdS5cPcA2A2M0A2S28G0S2aZ2Z27A2A2A2Sa0S36S9eA1S9cSbcSbbR3S62R1A3S5cA2A3A2Lms;LAi;AfFrho;").
Proof.
  intros rho Ai ms HF HP0 Hav HB HFF HN HD HZ HFR (r1 & t1 & m1 & HM) HT HTK. cbn [nd_tv nd_fr nd_bd ndR] in HN, HD, HZ, HFR.
  split; [|split; [|split; [|exact I]]].
  - eapply (robjs_checkA_sound segs AInv CST ALA FB Ai rho (ss_facts (ax_S E_m)) tv0 None (fun o => sv_eqb (ob_base o) vA) R_m None r1 t1 m1 HM HF HN HD HZ HTK).
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + intros o a Ho Hb Hr. eapply (P0_frame Ai rho Hav HP0 HFF). cbn in Ho.
      destruct Ho as [<-|[<-|[]]]; [cbn in Hb; discriminate|]. eapply (al_obj_range rho O_al a); [reflexivity | reflexivity | reflexivity | exact Hr].
    + exact I.
  - eapply (xrs_checkA_sound segs AInv CST XGL ALA FB Ai rho (ss_facts (ax_S E_m)) tv0 None (ss_objs (ax_S E_m)) (fun r => sv_eqb (fst r) vA) (ax_X E_m) None r1 t1 m1 HM HF HN HD HZ HTK).
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + intros r a Hr Hb Ha. left. eapply (P0_frame Ai rho Hav HP0 HFF). cbn in Hr.
      destruct Hr as [<-|[<-|[]]]; cbn in Hb; try discriminate. cbn [fst snd] in Ha. unfold uval in Ha. rewrite U_lit in Ha. change (48 mod M64v) with 48 in Ha. exact Ha.
    + exact I.
  - change (wsub_get s_m 12) with (kb16 vKn).
    fact HF (SPUle (SLit 1) vK) H3. fact HF (SPBranch BC_LTU vK vKn) H4. fact HF (SPUle vKn (SLit B32)) H5. zf H3. zf H4. zf H5.
    repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *. unfold B32 in *. rewrite uval_lit in H3, H5 by lia.
    rewrite kb16_exact by (unfold B32; lia). lia.
Qed.

Lemma site_f : ltac2:(tb__ "0|2|
SbSf5VAInv;VCST;VXGL;S90Vrho0;VP0;VFB;VFF;S56S5bS6cR1S49S47S4bA2S3aS5S7R1SbdS5bPcA2M0A2A2Sb8Sc4S0ScdR3S35ScScS46S45S44A1A4M1A2S0S1S33S5S5A2SceR3G1A2S35S5S5S7R3G0A2S7R3SbdS5bPdA2A2A4A3Sa0S36S9eA1S9cSbcSbbR3S6cR1A3S5bA2A3A2A2Lms;LAi;AfFrho;").
Proof.
  intros rho Ai ms HF HP0 Hav HB HFF HN HD HZ HFR (r1 & t1 & m1 & HM) HT HTK. cbn [nd_tv nd_fr nd_bd ndR] in HN, HD, HZ, HFR.
  change (wsub_get s_f 12) with vP. change (wsub_get s_f 13) with (kb16 vK).
  assert (Hnz : tnz rho (vP, kb16 vK)).
  { fact HF (SPUle (SLit 4096) vP) H18. unfold tnz. cbn [fst]. zf H18. rewrite uval_lit in H18 by lia. unfold uval, vP in *. lia. }
  split; [|split; [|split; [exact Hnz|split; [reflexivity|exact I]]]].
  - eapply (robjs_checkA_sound segs AInv CST ALA FB Ai rho (ss_facts (ax_S E_freeT)) tv1 (Some 1%nat) (fun o => sv_eqb (ob_base o) vA) R_f _ r1 t1 m1 HM HF HN HD HZ HTK).
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + intros o a Ho Hb Hr. eapply (P0_frame Ai rho Hav HP0 HFF). cbn in Ho.
      destruct Ho as [<-|[<-|[]]]; [cbn in Hb; discriminate|]. eapply (al_obj_range rho O_al a); [reflexivity | reflexivity | reflexivity | exact Hr].
    + exists (vP, kb16 vK). split; [reflexivity|]. split; [exact Hnz | reflexivity].
  - eapply (xrs_checkA_sound segs AInv CST XGL ALA FB Ai rho (ss_facts (ax_S E_freeT)) tv1 (Some 1%nat) (ss_objs (ax_S E_freeT)) (fun r => sv_eqb (fst r) vA) (ax_X E_freeT) _ r1 t1 m1 HM HF HN HD HZ HTK).
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + intros r a Hr Hb Ha. left. eapply (P0_frame Ai rho Hav HP0 HFF). cbn in Hr.
      destruct Hr as [<-|[<-|[]]]; cbn in Hb; try discriminate. cbn [fst snd] in Ha. unfold uval in Ha. rewrite U_lit in Ha. change (48 mod M64v) with 48 in Ha. exact Ha.
    + exists (vP, kb16 vK). split; [reflexivity|]. split; [exact Hnz | reflexivity].
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S5S32S41Q40A1A1SacF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S8eS2dSbS32S41Q40A1A1SacS9aS10SeR3A1SdS2cR4A1A1A3VTR;S8dS40R6R5R4R3A5R2A2M0F_;G0F_;FQa;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Qa : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Qa) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Qa.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
SacSacSacSadR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQa;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Qa : assn), (forall a, TR (P a) Qa) -> TR (fun w => exists a, P a w) Qa.
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
SacOSacSadR4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQa;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S8eS8eS2dS2dSbfS32SfA1M0S32S33S2dSb0A2M1A1S32S33ScScA2M2A1SacSbS32S41Q40A1A1M3G2Sb5G2R1R5A3Sb5G2R2S2fRbA1A3F_;Fr;S1S38G0A1Sb4RaR9R8A3S3aG0R7A2A3S1S31Sb3RbRaR9R8S9bG1S2dS3bS2dSb0A2R7A4A5S34A3SbG3VTR;S8dS40RfRdR2R1A5Sb1S40S14S2cRdA1A1R2R1RaA5A2Ftp1;Frho1;S32SbaA1M4Sc4Sb9S8fS40R9R8R10S35G4Sf1R3Sf2R2R1A2A4A5R13RaR9R4R2A4R13SbcSbbRbRfSc2R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S2dSb0G4Sc4Sb9SbG3G4Sc4Sb9Sb5G1S35S2dSb0RaR9A4R14A3S8fS40R12R11R19S35G4Sf1R9Sf2R8R7A2A4A5R1cR13R12RaR8A4Sc0S14S2cR1aA1A1SbcSbbR14R18Sc2R9R13RaA3A3R19A2R8A3S8fS40R9R8ReS35G4Sf1R7Sf2R6R5A2A4A5ReSbcSbbR16R1aSc2RbR15RcA3A3R1bA2R15RaR9R8R6A6S0SfdR17Sc2RcR16RdA3R1bR1cR1dR10R1eR19RbA9SbSc1R18Sc2RdR17ReA3R1cR1dS2cR1eA1S2cR1fA1S2cR11A1R1RcA9VTR;S8dS40Sb2R11SbcSbbR19R1dSc2ReR18RfA3A3R1eA2R18RdRcA5SfeR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S8dS40R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQa;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis TR_phi : ltac2:(tb__ "0|0|
SbOF_;S91S2dSbS32S41Q40A1A1SacR6R3A1VTR;S8dS40VJAv;R6A1R5R4R3A5R2A2F_;VTR;S8dS40Se5VAInv;VCST;VXGL;S90VKc;Vrho0;VP0;VFB;VFF;VBX;S92R7R6AdR5R4R3A5R2A2F_;FQa;Ftp;Frho;FS;Fnd;FPhi;").
Hypothesis CMALLOC : ltac2:(tb__ "0|1|
Sb8SbS32S41Q40A1A1VTR;S8dS40Sa2VAInv;S36S9eA1M0S9cR3VKc;S12PcA1A6Sa8S9dG0S9cA3R2R1A5Sb1S40S90R2R1Sa6S9dVAInv;VCST;VXGL;G0S9cR3VKc;A8A5A2Ftp1;Frho1;FAi;").
Hypothesis CFREE : ltac2:(tb__ "0|2|
Sb8SbS32S41Q40A1A1VTR;S8dS40Sa3VAInv;S36S9eA1M0S9cR3VKc;A5Sa7S9dG0S9cA3R2R1A5Sb1S40S90R2R1S39S33S2dSb0A2M1S35S2dSb0S9fS9dG0S9cA3Sa1VAInv;VCST;VXGL;R3VKc;A5A4S36G1A1A3A5A2Ftp1;Frho1;FAi;").

Hypothesis REENTER : ltac2:(tb__ "0|5|
S2dS91S37S33S5ScA2M0SbS32S41Q40A1A1M1S5G1Sb5S33S33S33S2dS91A2M2S37A2M3G0A2S35G3G0S35G2S37S35S2dS91R8R7A4R6A4R5A4S7aA3Se9Sc8R7R5A3S0S26Z0Se6S35G3G0S35G2S37S35S2dS91RaR9A4R8A4R7A4R6A2M4A2S28G4R4A2A2VTR;S8dS40VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|2|
S2dS91SbOF_;M0SbG0F_;SbS32S41Q40A1A1M1S5G1Sb5S33S2dSb0A2S35S2dSb0R8SeaVAInv;VCST;VXGL;VKc;VP0;VFB;VFF;VBX;S92R7R5AbA4Sc9A3SbR8R1A1R8Vrho0;R2A2F_;Fr;VTR;S8dS40Se5VAInv;VCST;VXGL;S90VKc;Vrho0;VP0;VFB;VFF;VBX;S92R8R9AdRaR6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;FPsi;FPhi;Fnd;FP;").

Lemma TR_phi_in : ltac2:(tb__ "0|0|
SbOF_;S91S2dSbS32S41Q40A1A1SacR6R3A1VTR;S8dS40Se5VAInv;VCST;VXGL;S90VKc;Vrho0;VP0;VFB;VFF;VBX;S92R7R6AdR5R4R3A5R2A2VTR;S8dS40VJAv;R7A1R6R5R4A5R3A2F_;F_;FQa;Ftp;Frho;FS;Fnd;FPhi;").
Proof. intros Phi nd S rho tp Qa HP H. eapply TR_pre; [|exact H]. intros w Hw. apply SPA_JAF_intro; [exact Hw | exact HP]. Qed.

Lemma X_E_m : ltac2:(tb__ "0|1|
SbS32S41Q40A1A1M0S5G0S26S29Z5aS2aZ2Z40A2A2R2A2VTR;S8dS40VJAFv;U0S49S54S65A2A2S61R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_phi. intros HPhi. apply TR_facts. intros HF.
  apply (TR_pureP _ (P0 rho0 /\ agree_vals NF rho0 rho)); [intros w Hw; exact (JA_P0 _ _ _ _ w Hw)|]. intros [HP0 Hav].
  fact HF (SPUle (SLit 4096) vP) H18. fact HF (SPBranch BC_LTU vK vKn) HKKn. fact HF (SPUle vKn (SLit B32)) HKB. zf H18. zf HKKn. zf HKB.
  rewrite uval_lit in H18 by lia. rewrite uval_lit in HKB by (unfold B32; lia).
  assert (EK : uval rho (kb16 vK) = 16 * uval rho vK) by (apply kb16_exact; lia).
  assert (Hnz : uval rho vP <> 0) by lia.
  apply (malloc_callT_k segs AE_A AInv CST XGL ALA HCST HXGL NF Kc rho0 P0 FB FF BX PTrue HKc HBX TR TR_facts TR_ex TR_pre TR_callP
           [] UStopLe E_m s_m R_m rho tp (ndR tv0 bd0) bd1 (FAM b tp0) CMALLOC).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - reflexivity.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - reflexivity.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - apply payA_of_bud_pay. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - intros A A_ _ _; exact I.
  - exact (site_m rho).
  - intros rho' tp' Hag HK. cbn [nd_tv nd_fr nd_am ndR]. fold Pre_m. rewrite T_mnull_eq.
    apply (REENTER T_mnull (ndR tv0 bd1) 0%nat (80, z0)); [innth 1 | | meas].
    exact (Phi0_keptR tv0 rho rho' ltac:(left; reflexivity) Hav Hnz EK HK HPhi).
  - intros rho' tp' Hag HK. cbn [nd_tv nd_fr nd_am ndR]. fold Pre_m. rewrite T_mok0_eq.
    eapply TR_pre; [|apply (REENTER T_mok (ndR tv1 bd1) 0%nat (80, z0)); [innth 2 | | meas]].
    + intros w Hw. unfold T_mok. apply (SPA_refacts_JA segs); [exact Hw | reflexivity |].
      intros tr md HJ HF'. apply Forall_app. split; [|exact HF'].
      eapply JA_tv_facts; [exact ALA | | exact HJ | left; reflexivity |]; [reflexivity|].
      fact HF' (SPNot (SPBranch BC_EQ (SVar pN) (SLit 0))) Hnz'. eapply tnz_of_fact. exact Hnz'.
    + exact (Phi0_keptR tv0 rho rho' ltac:(left; reflexivity) Hav Hnz EK HK HPhi).
Qed.

Lemma X_X_cp0 : ltac2:(tb__ "0|1|
SbS32S41Q40A1A1M0S5G0S26S29Z4bS2aZ2Z40A2A2R2A2VTR;S8dS40VJAFv;U0S49S47S4bA2A2S58R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_phi. intros HPhi.
  apply (TR_pre (fun w => exists r', (Phi1 r' /\ uval r' vK = uval rho vK /\ uval r' vQ = 0 /\ 1 <= uval rho vK <= B32) /\ SPA segs (JAv (ndR tv1 bd1)) C_0 r' tp w)).
  { intros w Hw. destruct (cp0_glue rho tp w HPhi Hw) as (r' & H1 & H2 & H3 & H4 & H5). exists r'. auto. }
  apply TR_exw; intros r'. eapply TR_pureP; [intros w [H _]; exact H|]. intros (HP1 & EK & EQ & HK).
  eapply TR_pre; [intros w [_ Hw]; exact Hw|].
  apply (REENTER C_0 (ndR tv1 bd1) 1%nat (70, VQ 0) r'); [innth 3 | exact HP1 |].
  rewrite (meas_VQ C_0 _ 1%nat 70 0 r') by (rewrite ?EK, ?EQ; lia). rewrite EK, EQ. unfold two47, B32 in *. lia.
Qed.

Lemma X_X_step : ltac2:(tb__ "0|4|
SbS32S41Q40A1A1M0S5G0S26Se6S35S33S33S2dS91A2M1S37A2S33S5ScA2S35G1S37S35S2dS91S53S49S47S4bA2M2A4U1M3A4S35S5ScZ46S6dZ1fA1A4A4R4A2R2A2VTR;S8dS40VJAFv;G3G2A2S53R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_phi. intros HPhi.
  apply (TR_pre (fun w => exists r', (Phi1 r' /\ uval r' vK = uval rho vK /\ uval r' vQ = uval rho vQ + 1 /\ uval rho vQ + 1 < uval rho vK /\ uval rho vK <= B32)
                                     /\ SPA segs (JAv (ndR tv1 bd1)) C_0 r' tp w)).
  { intros w Hw. destruct (step_glue rho tp w HPhi Hw) as (r' & H1 & H2 & H3 & H4 & H5 & H6). exists r'. auto 10. }
  apply TR_exw; intros r'. eapply TR_pureP; [intros w [H _]; exact H|]. intros (HP1 & EK & EQ & HqK & HKB).
  eapply TR_pre; [intros w [_ Hw]; exact Hw|].
  apply (REENTER C_0 (ndR tv1 bd1) 1%nat (70, VQ 0) r'); [innth 3 | exact HP1 |].
  rewrite (meas_VQ X_step _ 1%nat 70 31 rho) in Hb by lia.
  rewrite (meas_VQ C_0 _ 1%nat 70 0 r') by (rewrite ?EK, ?EQ; lia). rewrite EK, EQ. unfold two47, B32 in *. lia.
Qed.

Lemma X_E_free : ltac2:(tb__ "0|1|
SbS32S41Q40A1A1M0S5G0S26S29Z41S2aZ2Z40A2A2R2A2VTR;S8dS40VJAFv;U1S49S47S4bA2A2S5fR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_phi. intros HPhi.
  apply (TR_pre (fun w => exists r', (Phi2 r' /\ uval r' (SVar pN) <> 0 /\ uval r' (kb16 vKn) = 16 * Kn0 /\ K0 < Kn0) /\ SPA segs (JAv (ndR tv1 bd1)) E_freeT r' tp w)).
  { intros w Hw. destruct (free_glue rho tp w HPhi Hw) as (r' & H1 & H2 & H3 & H4 & H5). exists r'. auto 6. }
  apply TR_exw; intros r'. eapply TR_pureP; [intros w [H _]; exact H|]. intros (HP2 & Hnz & HKK & HKn).
  eapply TR_pre; [intros w [_ Hw]; exact Hw|].
  apply (free_callT_k segs AE_A AInv CST XGL ALA HCST HXGL NF Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           [] UStopLe E_freeT s_f R_f r' tp (ndR tv1 bd1) 1%nat (vP, kb16 vK) [] (FAM b tp0) CFREE).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - reflexivity.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - reflexivity.
  - reflexivity.
  - apply payA_of_bud_pay. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - intros A A_ _ _; exact I.
  - exact (site_f r').
  - intros rho' tp' Hag HK. cbn [nd_tv nd_fr nd_am ndR remove_nth]. fold Pre_f. rewrite T_free_eq.
    apply (REENTER T_free (ndR tv2 []) 2%nat (60, z0)); [innth 19 | | meas].

    assert (E111 : uval rho' (SVar pN) = uval r' (SVar pN)) by (unfold uval; cbn [eval]; rewrite <- (proj1 Hag pN ltac:(reflexivity)); reflexivity).
    assert (KEEP : forall j, 0 <= j < 16 * Kn0 -> rm rho' (Z_to_bv 64 (uval r' (SVar pN) + j)) = rm r' (Z_to_bv 64 (uval r' (SVar pN) + j))).
    { intros j Hj. apply (HK (SVar pN, kb16 vKn) (uval r' (SVar pN) + j) ltac:(left; reflexivity)); [unfold tnz; cbn [fst]; exact Hnz |].
      unfold tvv. cbn [fst snd]. repeat change (bv_unsigned (eval r' ?e)) with (uval r' e). lia. }
    change (Phi2 rho'). unfold Phi2. rewrite E111. destruct HP2 as [HP2a HP2b]. pose proof (uval_range rho0 vK) as RK0. unfold K0, Kn0 in *.
    split; intros j Hj; rewrite KEEP by lia; [exact (HP2a j Hj) | exact (HP2b j Hj)].
Qed.

Lemma X_P_fail : ltac2:(tb__ "0|1|
SbS32S41Q40A1A1M0S5G0VTR;S8dS40VJAFv;U0S49S54S36S9A1A2A2S74R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0. apply (POST P_fail (ndR tv0 []) (phiK Phis 0) Psi_fail); [left; reflexivity|].
  intros r Hr z Hz. exact (Hr z Hz).
Qed.

Lemma X_P_okX : ltac2:(tb__ "0|1|
SbS32S41Q40A1A1M0S5G0VTR;S8dS40VJAFv;U2S49S72S36S9A1A2A2S6bR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0. apply TR_phi. intros HPhi.
  apply (TR_pureP _ (P0 rho0 /\ agree_vals NF rho0 rho)); [intros w Hw; exact (JA_P0 _ _ _ _ w Hw)|]. intros [HP0 Hav].
  pose proof chk_post as (Cent & Cid & Ctv & Cnb & Cbud).
  apply (TR_pre (SPA segs (JAv (ndR tvP [])) P_ok (rho_sub rho s_post) tp)).
  { intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc P_okX P_ok s_post (ndR tv2 []) (ndR tvP []) rho tp w Cent Cid);
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact Cnb | exact Ctv | reflexivity | exact Cbud | reflexivity | exact Hw]. }
  apply (TR_phi_in (fun r => Psi_ok rho0 r) (ndR tvP []) P_ok (rho_sub rho s_post) tp).
  - assert (E140 : uval (rho_sub rho s_post) vPn = uval rho (SVar pN)) by reflexivity.
    assert (EM : rm (rho_sub rho s_post) = rm rho) by reflexivity. unfold Psi_ok. rewrite E140, EM. destruct HPhi as [HPa HPb]. split.
    + intros j Hj. split; [exact (HPa j Hj) | apply (proj2 HP0); unfold ptr0, K0 in Hj |- *; lia].
    + intros j Hj. exact (HPb j Hj).
  - apply (POST P_ok (ndR tvP []) (fun r => Psi_ok rho0 r) Psi_ok); [right; left; reflexivity | intros r Hr; exact Hr].
Qed.

Lemma exits_okT : ltac2:(tb__ "0|4|
S2dS91S37S33S5ScA2M0SbS32S41Q40A1A1M1G1Sb5S33S33S33S2dS91A2M2S37A2M3G0A2S35G3G0S35G2S37S35S2dS91R7R6A4R5A4R4A4S7bA3VTR;S8dS40VJAFv;R6R7A2R8R4R3A5VFAM;Se6S35G3G0S35G2S37S35S2dS91R8R7A4R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FkX;FndX;FX;").
Proof.
  intros X ndX kX rvX rho tp tp0 Hin. cbn in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[]]]]]]]; injection H as <- <- <- <-.
  - apply X_E_m. meas.
  - apply X_X_cp0. meas.
  - apply X_X_step. lia.
  - apply X_E_free. meas.
  - apply X_P_fail.
  - apply X_P_okX.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S98S40VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
Sa9S40S9dVAInv;VCST;VXGL;A5").

Theorem realloc_rom_sum : ltac2:(tb__ "0|0|
S32S41Q40A1A1SafS40Vok;S8dS40S94VAInv;VCST;VXGL;VKc;S6aVFB;VFF;A2VFB;VFF;VBX;S92S49S54S65A2AaS77Vrho0;R1A5Sb1S40S90Vrho0;R1Sc9A5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JAF segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc Phis Phis_reads FUEL_rr cutpcs_rr 100
                (map efdrop cutsE) (map efdrop exitsE) ok (Q tp0) Hok (ejcertAF_jcertAF segs NF Phis _ _ _ _ _ ejcertAF_ok))
         with (ndT := ndR tv0 bd0) (kT := 0%nat); [|left; reflexivity].
       intros X ndX kX rho tp Hin. apply in_map_iff in Hin as ([[[X' nd'] k'] rv] & E0 & Hin). cbn in E0. injection E0 as <- <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map (nodeIAF AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phis) (map efdrop cutsE)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)) with (rvX := rv) (tp0 := tp0).
       - intros Phi nd S rho1 tp1 Qa H. exact (triple_JAF segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phi ok nd S rho1 tp1 Qa H).
       - intros Ai rho1 tp1. apply (aca_malloc _ _ _ _ _ AC); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc| |]. exact (proj1 Hok). exact (proj2 Hok).
       - intros Ai rho1 tp1. apply (aca_free _ _ _ _ _ AC); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc| |]. exact (proj1 Hok). exact (proj2 Hok).
       - intros T nd k rv' rho1 tp1 b tp2 HinT HP _. apply (reenter_cutJAF segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phis ok (map efdrop cutsE) T nd k); [|exact HP].
         apply in_map_iff. exists (T, nd, k, rv'). auto.
       - intros P nd Phi Psi rho1 tp1 b tp2 HinP HPsi. apply (exit_postGAF segs AInv CST XGL NF Kc P0 FB FF BX PTrue ok rho0 tp0 Phi Psi nd Posts_rr P); [exact HinP | exact HPsi].
       - exact Hin. }
  intros w Hw. apply SPA_JAF_intro; [apply JA_pre_intro; exact Hw|]. intros z Hz. reflexivity.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
SaaS40S9dVAInv;VCST;VXGL;A5").

Theorem realloc_rom_sum_ex : ltac2:(tb__ "0|0|
S32S41Q40A1A1SaeS40S8dS40S94VAInv;VCST;VXGL;VKc;S6aVFB;VFF;A2VFB;VFF;VBX;S92S49S54S65A2AaS77Vrho0;R1A5Sb1S40S90Vrho0;R1Sc9A5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JAF segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc Phis Phis_reads FUEL_rr cutpcs_rr 100 cutsE exitsE (Q tp0) ejcertAF_ok)
         with (ndT := ndR tv0 bd0) (kT := 0%nat) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX kX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIAF AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phis) cutsE) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (@etriple_ex segs) (TRe_pureP segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros Phi nd S rho1 tp1 Qa H. exact (etriple_JAF segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phi nd S rho1 tp1 Qa H).
       - intros Ai rho1 tp1. apply (acx_malloc _ _ _ _ _ ACX); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc].
       - intros Ai rho1 tp1. apply (acx_free _ _ _ _ _ ACX); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc].
       - intros T nd k rv' rho1 tp1 b tp2 HinT HP Hm. apply (ereenter_cutJAF segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phis cutsE T nd k rv'); [exact HinT | exact HP | exact Hm].
       - intros P nd Phi Psi rho1 tp1 b tp2 HinP HPsi. apply (eexit_postGAF segs AInv CST XGL NF Kc P0 FB FF BX PTrue rho0 tp0 Phi Psi nd Posts_rr P); [exact HinP | exact HPsi].
       - exact Hin. }
  intros w Hw. apply SPA_JAF_intro; [apply JA_pre_intro; exact Hw|]. intros z Hz. reflexivity.
Qed.
End Existence.
End Sum.

Print Assumptions realloc_rom_sum.
Print Assumptions realloc_rom_sum_ex.
End Lib_realloc_rom_pf.

(* [comment removed for export] *)
Module Lib_handle_vn_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "True"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_setS"; "leafA"; "g8"; "la_state"; "has_facts"; "ax_base"; "@Corelib.Init.Datatypes"; "cons"; "list"; "prod"; "bool"; "true"; "pair"; "nat"; "nil"; "Some"; "option"; "fst"; "None"; "snd"; "app"; "andb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "valuation"; "sobj"; "SPUle"; "ss_facts"; "SVar"; "ss_next"; "SAlu"; "ss_objs"; "holds"; "sprop_eqb"; "cell"; "DUnknown"; "mkObj"; "rw"; "obj_range"; "obj_wf"; "soff"; "SPEq"; "sv_eqb"; "DZero"; "ob_base"; "ob_hi"; "ob_lo"; "sprop_below"; "swf"; "SMd"; "agree_below"; "mkCell"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXSelect"; "AXMerge"; "AXUnbase"; "AXSplit"; "@Stdlib.ZArith.BinInt.Z"; "le"; "pow"; "mul"; "lt"; "add"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "ANone"; "NDA"; "PTrue"; "nd_below"; "TPA"; "edescA"; "frinA"; "tvinA"; "JA_pre"; "fbinA"; "ffinA"; "ND"; "emeasA"; "JA"; "JLA"; "ejcertA"; "frozen"; "nodeIA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "bitem"; "bd_subst"; "bd_wpos"; "BXok_d"; "bd_below"; "bxt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_vn"; "fr_hvn"; "vF"; "E_vr"; "gF"; "s_v"; "cutsH"; "ndp"; "E_B"; "E_C"; "L_mc1"; "Pre_mc"; "epi_state"; "E_A"; "R_v"; "optAh"; "sel_rel"; "E_mg0"; "E_mk0"; "T_sm1"; "Xk_v"; "ndf"; "vDg"; "vKg"; "xf_mc"; "C_pro0"; "E_mg"; "E_mk"; "P_fail"; "P_ok"; "T_grown0"; "T_keep0"; "X_epi"; "exitsH"; "nd0"; "nd_fail"; "nd_ok"; "ndg"; "ndk"; "slot_facts"; "C_ms1"; "E_A0"; "E_sm0"; "E_vr0"; "L_ms"; "Pre_hvn"; "Pre_ms"; "R_A"; "R_B"; "R_C"; "T_ms0"; "T_sm"; "X_epf0"; "X_epf1"; "X_epg"; "X_epk"; "X_hvn"; "X_rel"; "X_rlf0"; "X_rlf1"; "X_rlg"; "X_rlk"; "Y_epf0"; "Y_epf1"; "Y_epg"; "Y_epk"; "bd_hvn"; "dst_obj"; "objs_sm1"; "s_A"; "s_B"; "s_C"; "s_mc"; "src_obj"; "tv_hvn"; "C_body"; "C_epf0"; "C_epf1"; "C_epg"; "C_epk"; "C_ms"; "C_pro"; "E_ms"; "FUEL_hvn"; "L_sm"; "Pre_sm"; "R_mg"; "R_mk"; "R_ms"; "R_sm"; "T_A0"; "T_A1"; "T_B0"; "T_B1"; "T_C0"; "T_C1"; "T_fail0"; "T_grown"; "T_keep"; "T_mcg"; "T_mck"; "T_ms1"; "cutpcs_hvn"; "objs_rel"; "s_ms"; "s_sm"; "sel_ms"; "sel_sm"; "tvG"; "xf_sd"; "xf_vr"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Lib_handle_vn_pf"; "P0_hvn"; "baseF"; "extraO"; "frameF"; "E_mc2"; "cm1"; "extraX"; "E_mc1"; "basez"; "E_mc3"; "cm2"; "in_callers"; "xf_cm"; "cm_dst"; "cm_src"; "vb184"; "xf_cf"; "PD_vr"; "base_facts"; "cells_rel"; "extra_tab"; "frame_facts"; "framez"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "import_postA"; "LQPA";
"import_subA"; "entails_frA"; "call_checkA"; "call_checkPA"; "J_ofPA"; "@Stdlib.Lists.List"; "existsb"; "In"; "nth_error"; "forallb"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs"; "vNK"; "vND"; "vb"; "vNC"; "vAL"; "cb4"; "kb4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double"; "Pre_sd"; "vB"; "vL"; "P_none"; "P_num"; "Posts_sd"; "two26"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "Pre_vr"; "z0"; "B32"; "P_grown"; "P_keep"; "P_fail"; "bdP"; "tv0"; "vW"; "nd0"; "tvP"; "vKn"; "two47"; "vK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "fs_frame_size"; "SHADOW_OFF"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double.ScanDoubleAddr"; "pow10_tab"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_ok"; "FBx"; "tvd"; "tvz"; "import_tv"; "remove_nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "pclMA"; "FFx"; "T_afterA3"; "PostsC"; "robjs_okF"; "xrs_inclb"; "xrs_okF"; "xrs_okL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "ccount"; "is_shadowZ"; "call_checkTA"; "payA"; "robjs_okA"; "site_okA"; "xrs_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Lib_handle_vn_pf.Sum"; "Posts_hvn"; "JLh"; "H_ejcertH_ok"; "keep_ejcertH_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "xrs_checkL"; "robjs_checkF"; "shobj"; "frame_open_stateA"; "release_objs_ok"; "shadow_reopen_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "JL_pure"; "JL_stack_malloc"; "J_memcpy_pre"; "J_memset_pre"; "J_stack_malloc_pre"; "L_stack_malloc"; "Pre_stack_malloc"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "flagbyte_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_vec_reserve_pf"; "P0_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT"; "robjs_checkP"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_vn.HVNAddr"; "DW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA"; "hideE"; "hide_setE";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "robjs_okF"; "xrs_ok47"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAT HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.Lib_scan_double_ex.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_vn.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_vec_reserve_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_vn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr HVNAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition P0_hvn (CST : list (Z * Z)) (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|4|
S1S3cS1S47S40Q40M0S2dVr;PfA2A2M1R1A2S4aR1S4bG1S40G0S2dVr;P12A2A2A2A2A2S13cVCST;Vr;VFB;VFF;R2A5F_;Fa;S1S151VFF;S40G0S2dVr;PcA2A2Z518A3S1S151VFF;S40G0S2dVr;P3aA2A2Z30A3S1S3S0S3cS40G0S2dVr;P38A2A2Z0M2A3A1S3S0S3cS40G0S2dVr;P36A2A2G2A3A1F_;S0S14S145G2S101S10S10S3cS3cA2M3S3cA2G3S18G3S3cA2VFF;A4A2U0A3A2A2A2A2").

Definition cm_dst (d : sv) : sobj := ltac2:(tb__ "0|1|
S2cVd;S109S107A1M0S26SdbG0S1fZcA1A3S15S2aA1S2bA5").
Definition cm_src : sobj := ltac2:(tb__ "0|0|
S2cS6eS1fZ20A1S1fZ2cA1S15S2aA1S2bA5").
Definition cm1 (A : axst) (d : sv) : axst := ltac2:(tb__ "0|0|
S8VA;S150S6VA;A1U1SeaVd;A1A3A2").
Definition cm2 (A : axst) : axst := ltac2:(tb__ "0|0|
S8VA;S150S6VA;A1U2SebA3A2").
Definition xf_cm : list axform := ltac2:(tb__ "0|7|
SeS41S45UbM0Z68A2SeS41S45U5M1Nb8A2SeS41S43SeS14U0SeS14UcSeS14U2SeS14UdM2SeS14UeSeS14U3SeS14U4SeS14UfSeS14G0SeS14U10SeS14U11SeS14U12SeS14G1SeS14U6SeS14U9SeS14U13SeS14UaSeS14U7SeS14U1M3SeS14U8S15S14A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1SeS41S44G3A1M4SeS41G4SeS41S44G1A1M5SeS41G5SeS41S44G2A1M6SeS41G6S15S41A1A3A3A3A3A3A3A3A3A3").
Definition xf_cf : list axform := ltac2:(tb__ "0|6|
SeS41S45U1M0Z40A2SeS41S45U9M1Z68A2SeS41S45U2M2Nb8A2SeS41S43SeS14G0SeS14U0M3SeS14UaSeS14UbSeS14U5M4SeS14U6SeS14UcSeS14G1SeS14UdSeS14UeSeS14UfSeS14G2SeS14U3SeS14U7SeS14U10SeS14U8SeS14U4S15S14A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1SeS41S44G3A1SeS41S44G4A1M5SeS41G5S15S41A1A3A3A3A3A3A3A3").
Lemma Y_epk_eq : ltac2:(tb__ "0|0|
S0S17S5A1S42Se7Se2Sa3S105A2A1Se9A2S16S5SadA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Y_epg_eq : ltac2:(tb__ "0|0|
S0S17S5A1S42Se7Se2Sa2S82A2A1Se9A2S16S5SacA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Y_epf0_eq : ltac2:(tb__ "0|0|
S0S17S5A1S42Sa0SedA2S16S5SaaA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Y_epf1_eq : ltac2:(tb__ "0|0|
S0S17S5A1S42Sa1SedA2S16S5SabA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_epk_eq : ltac2:(tb__ "0|0|
S0S5S78SadS105S104A3SbbA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_epg_eq : ltac2:(tb__ "0|0|
S0S5S78SacS82S83A3SbaA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_epf0_eq : ltac2:(tb__ "0|0|
S0S5S78SaaS105S104A3Sb8A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_epf1_eq : ltac2:(tb__ "0|0|
S0S5S78SabS105S104A3Sb9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_A_eq : ltac2:(tb__ "0|0|
S0S17S5A1S42S95Sd9A2S16S5S79A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_B_eq : ltac2:(tb__ "0|0|
S0S17S5A1S42S74S15S41A1A2S16S5S74A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_C_eq : ltac2:(tb__ "0|0|
S0S17S5A1S42S75S15S41A1A2S16S5S75A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_A0_eq : ltac2:(tb__ "0|0|
S0S5S127S23S6S79A1A1Sf5Sb1S10bS10eS79S9bA5A2Sc6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_A1_eq : ltac2:(tb__ "0|0|
S0S5S127S23S6S79A1A1Sf5Sb1S10bS10fS79S9bA5A2Sc7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_B0_eq : ltac2:(tb__ "0|0|
S0S5S127S23S6S74A1A1Sf5Sb2S10bS10eS74S9cA5A2Sc8A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_B1_eq : ltac2:(tb__ "0|0|
S0S5S127S23S6S74A1A1Sf5Sb2S10bS10fS74S9cA5A2Sc9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_C0_eq : ltac2:(tb__ "0|0|
S0S5S127S23S6S75A1A1Sf5Sb3S10bS10eS75S9dA5A2ScaA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_C1_eq : ltac2:(tb__ "0|0|
S0S5S127S23S6S75A1A1Sf5Sb3S10bS10fS75S9dA5A2ScbA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition E_mc1 (E0 : axst) : axst := ltac2:(tb__ "0|0|
S7bS42VE0;S84A2A1").
Definition E_mc2 (E1 : axst) (d : sv) : axst := ltac2:(tb__ "0|0|
S8VE1;S150S6VE1;A1U4SafVd;A1A3A2").
Definition E_mc3 (E2 : axst) : axst := ltac2:(tb__ "0|0|
S8VE2;S150S6VE2;A1UcSb5A3A2").
Lemma E_mk1_eq : ltac2:(tb__ "0|0|
S0S17S5A1S42S7eS84A2S16S5Se4S7eA1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_mg1_eq : ltac2:(tb__ "0|0|
S0S17S5A1S42S7dS84A2S16S5Se4S7dA1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_mk_eq : ltac2:(tb__ "0|0|
S0S5Se6Se1Se4S7eA1S105A2A1S87A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_mg_eq : ltac2:(tb__ "0|0|
S0S5Se6Se1Se4S7dA1S82A2A1S86A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mck_eq : ltac2:(tb__ "0|0|
S0S5S144S77S87Sb4S87S105S104A3Sc3S76A5Sd0A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mcg_eq : ltac2:(tb__ "0|0|
S0S5S144S77S86Sb4S86S82S83A3Sc2S76A5ScfA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition cells_rel : list cell := Eval vm_compute in ob_cells sh_rel.
Lemma X_rel_objs : ltac2:(tb__ "0|0|
S0SfS21A1S27S6Sa5A1A1S1bS21Sd3SeS21S154S70Z0Z8Sf0S33A5S15S21A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_ms1_eq : ltac2:(tb__ "0|0|
S0S17S5A1S42SbcSeS41S46U1S1fZ20A1A2SeS41S46U2S1fZ2cA1A2S15S41A1A3A3A2S16S5S94A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_ms1_o2 : ltac2:(tb__ "0|0|
S0S17S21A1SfeS21S27S6S94A1A1U2A3S16S21S2cS6eS1fZ20A1S1fZ2cA1S15S2aA1S2bA5A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_ms0_eq : ltac2:(tb__ "0|0|
S0S5S144S9aSbeSd4Sc4S98A5S9eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_ms0_o1 : ltac2:(tb__ "0|0|
S0S17S21A1SfeS21S27S6S9eA1A1U1A3S16S21S2cS26SdbS6eS1fZ20A1A3S1fZ0A1S1fZcA1S15S2aA1S33A5A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_body_eq : ltac2:(tb__ "0|1|
S0S17S5A1S42Sd1SeS41S43Sd6A1SeS41S44U1A1M0SeS41G0S15S41A1A3A3A3A2S16S5Sb7A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_sm_eq : ltac2:(tb__ "0|1|
S0S5S144S15fS158Z0M0A2S96Sd5Sc5S15eS158G0A2A5S9fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_sm1_eq : ltac2:(tb__ "0|0|
S0S17S5A1S42S9fSeS41S43Sd7A1S15S41A1A3A2S16S5S7fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_sm1_objs : ltac2:(tb__ "0|1|
S0SfS21A1S27S6S7fA1A1S1bS21Sb0SeS21S163S24P78A1SeS2aS3bS1fZ0A1Z1M0S1fG0A1A3S15S2aA1A3A2S15S21A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_sm1_X : ltac2:(tb__ "0|1|
S0SfS10S1dS1dA2M0A1S7S7fA1S1bG0Sa4S105S104A2SeG0S13S1dS1dS24P6eA1S1fS12fZ0A1A1A4S15G0A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_pro0_eq : ltac2:(tb__ "0|0|
S0S5S155S7fSb0Sa4S105S104A2P6eS12fZ0A1A5S85A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_pro_eq : ltac2:(tb__ "0|0|
S0S5S16cS85SeS10S1dS1dA2S13S1dS1dS24P6eA1S1fZ0A1A4S7S85A1A3A2SbdA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_vr_eq : ltac2:(tb__ "0|0|
S0S17S5A1S42S97SdaA2S16S5S6fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition PD_vr : list (axst * ndesc) := ltac2:(tb__ "0|2|
SeS10S5S51A2M0S13S5S51S11bS120A4SeG0S13S5S51S11cS5dS11eS15S10S10S1dS3cA2S1dA2A1M1S15S67A1A3A4SeG0S13S5S51S11aS5dS121G1S11dS11fS122A2A3A4S15G0A1A3A3A3").
Lemma T_keep0_eq : ltac2:(tb__ "0|0|
S0S5S13eS117S6fS71S7aS11bS80A6S8bA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_fail0_eq : ltac2:(tb__ "0|0|
S0S5S13eS117S6fS71S7aS11cS80A6SccA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grown0_eq : ltac2:(tb__ "0|0|
S0S5S13eS117S6fS71S7aS11aS80A6S8aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keep_eq : ltac2:(tb__ "0|0|
S0S5S16bS8bS1bS1eS1bS1eS93S104A1SeS1eS22S1fS12eA1S105A2S15S1eA1A3A3S23S6S8bA1A1A3A2SceA3"). Proof. reflexivity. Qed.
Lemma T_grown_eq : ltac2:(tb__ "0|0|
S0S5S16bS8aS1bS1eS93S83A1S23S6S8aA1A1A3A2ScdA3"). Proof. reflexivity. Qed.
Lemma imp_keep_tv : ltac2:(tb__ "0|0|
S0SfS10S1dS1dA2A1S13aSf7S71S117S11bS6fA4S11eA2Sb6S105S104A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_keep_bd : ltac2:(tb__ "0|0|
S0SfS67A1S68Sf7S71S117S11bS6fA4S11dS11fS124A2A2SaeS107S104A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_fail_tv : ltac2:(tb__ "0|0|
S0SfS10S1dS1dA2A1S13aSf7S71S117S11cS6fA4S11eA2Sb6S105S104A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown_tv : ltac2:(tb__ "0|0|
S0SfS10S1dS1dA2A1S13aSf7S71S117S11aS6fA4S121A2Sd8A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown_bd : ltac2:(tb__ "0|0|
S0SfS67A1S68Sf7S71S117S11aS6fA4S11dS11fS122A2A2SaeS107S83A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_rlk_eq : ltac2:(tb__ "0|1|
S0S17S5A1S42Sa9SeS41S43S7cA1S15S41A1A3A2M0S16S5S7bG0A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_rlg_eq : ltac2:(tb__ "0|1|
S0S17S5A1S42Sa8SeS41S43S7cA1S15S41A1A3A2M0S16S5S7bG0A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_rlf0_eq : ltac2:(tb__ "0|1|
S0S17S5A1S42Sa6SeS41S43S7cA1S15S41A1A3A2M0S16S5S7bG0A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_rlf1_eq : ltac2:(tb__ "0|1|
S0S17S5A1S42Sa7SeS41S43S7cA1S15S41A1A3A2M0S16S5S7bG0A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition base_facts : list sprop := ltac2:(tb__ "0|4|
SeS1eS22S24PaA1M0S1fS123A1M1A2SeS1eS22S26SdbS24P1eA1M2S1fS16dA1A3G0A2SeS1eS22S1fS12eA1M3S106A2SeS1eS22S26SdbS106S1fZ518A1A3G2A2SeS1eS22S106G1A2SeS1eS22G3S108A2SeS1eS22S26SdbS108S1fZ30A1A3G2A2SeS1eS22S108G1A2SeS1eS22S10dS1fS111A1A2SeS1eS22S10cG1A2SeS1eS22S1fZ7fff7f800000A1G2A2SeS1eS22G2S1fZ7fffff800000A1A2S15S1eA1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition baseF (F : list sprop) : bool := ltac2:(tb__ "0|0|
SffS1eS1eSfcS1eS29R1A1VF;A3Lp;SefA3").

Definition frame_facts : list sprop := ltac2:(tb__ "0|2|
SeS1eS31SaS70A1S6eA2SeS1eS22S24S70A1S1fS4cS48Z2M0Z3dA2Z1A2A1A2SeS1eS22S1fS12eA1S6eA2SeS1eS22S26SdbS6eS1fZ40A1A3S24P1eA1M1A2SeS1eS22S6eS1fS48G0Z2fA2A1A2SeS1eS22G1S1fZ7fffff800000A1A2S15S1eA1A3A3A3A3A3A3").
Definition frameF (F : list sprop) : bool := ltac2:(tb__ "0|0|
SffS1eS1eSfcS1eS29R1A1VF;A3Lp;Sf2A3").

Record basez (rho : valuation) : Prop := BZ {
  bz_sp : aceil + DW <= uval rho (SVar 10) <= 2 ^ 47;
  bz_b : IMG_HI <= uval rho vb /\ uval rho vb + 1304 <= bv_unsigned (rw rho V_TOP);
  bz_al : IMG_HI <= uval rho vAL /\ uval rho vAL + 48 <= bv_unsigned (rw rho V_TOP);
  bz_L : uval rho vL <= 2 ^ 26;
  bz_B : uval rho vB <= 2 ^ 47;
  bz_top : bv_unsigned (rw rho V_TOP) + DW <= uval rho (SVar 10) /\ 140735332483072 <= bv_unsigned (rw rho V_TOP) <= 140737479966720 }.
Record framez (rho : valuation) : Prop := FZ {
  fz_g : uval rho (SVar gF) = uval rho vF / 8;
  fz_g8 : uval rho vF mod 8 = 0;
  fz_f : IMG_HI <= uval rho vF /\ uval rho vF + 64 <= bv_unsigned (rw rho V_TOP) /\ bv_unsigned (rw rho V_TOP) <= 140737479966720 }.

Lemma uval_add_litZ : ltac2:(tb__ "0|0|
S20S1dS3cS47Z0R1A2S4aS4bS66R4R3A2R2A2S48Z2Z40A2A2S0S3cS66R5S26SdbR4S1fR3A1A3A2S4bS66R5R4A2R3A2A3F_;F_;Fk;Fa;Frho;").
Proof. intros rho a k Hk H. pose proof (uval_range rho a). rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity. Qed.

Lemma basez_of : ltac2:(tb__ "0|0|
S20SfS1eA1S100S1eS28R2A1R1A3S0S11SdeR2A1S12A3Se5R4A1F_;F_;FF;Frho;").
Proof.
  intros rho F HF HB. unfold baseF in HB.
  assert (G : forall p, In p base_facts -> holds rho p).
  { intros p Hp. apply (holds_mem rho F p HF). exact (proj1 (forallb_forall _ _) HB p Hp). }
  cbn [base_facts] in G.
  pose proof (G _ ltac:(left; reflexivity)) as F1. pose proof (G _ ltac:(do 1 right; left; reflexivity)) as F2.
  pose proof (G _ ltac:(do 2 right; left; reflexivity)) as F3. pose proof (G _ ltac:(do 3 right; left; reflexivity)) as F4.
  pose proof (G _ ltac:(do 4 right; left; reflexivity)) as F5. pose proof (G _ ltac:(do 5 right; left; reflexivity)) as F6.
  pose proof (G _ ltac:(do 6 right; left; reflexivity)) as F7. pose proof (G _ ltac:(do 7 right; left; reflexivity)) as F8.
  pose proof (G _ ltac:(do 8 right; left; reflexivity)) as F9. pose proof (G _ ltac:(do 9 right; left; reflexivity)) as F10.
  pose proof (G _ ltac:(do 10 right; left; reflexivity)) as F11. pose proof (G _ ltac:(do 11 right; left; reflexivity)) as F12.
  rewrite h_ule in F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12.
  unfold two47, two26, RA.two47 in *. unfold DW, IMG_HI in *.
  rewrite !uval_lit in * by lia. pose proof (uval_range rho (SVar 30)) as R30. rewrite uval_add_litZ in F2 by lia.
  change (uval rho (SVar 30)) with (bv_unsigned (rw rho V_TOP)) in *.
  pose proof (uval_range rho vb) as Rb. pose proof (uval_range rho vAL) as Ral.
  rewrite uval_add_litZ in F4 by lia. rewrite uval_add_litZ in F7 by lia.
  constructor; rewrite ?aceil_val; unfold DW, IMG_HI in *; lia.
Qed.

Lemma framez_of : ltac2:(tb__ "0|0|
S20SfS1eA1S100S1eS28R2A1R1A3S0S11Se0R2A1S12A3Sf3R4A1F_;F_;FF;Frho;").
Proof.
  intros rho F HF HB. unfold frameF in HB.
  assert (G : forall p, In p frame_facts -> holds rho p).
  { intros p Hp. apply (holds_mem rho F p HF). exact (proj1 (forallb_forall _ _) HB p Hp). }
  cbn [frame_facts] in G.
  pose proof (G _ ltac:(left; reflexivity)) as F1. pose proof (G _ ltac:(do 1 right; left; reflexivity)) as F2.
  pose proof (G _ ltac:(do 2 right; left; reflexivity)) as F3. pose proof (G _ ltac:(do 3 right; left; reflexivity)) as F4.
  pose proof (G _ ltac:(do 4 right; left; reflexivity)) as F5. pose proof (G _ ltac:(do 5 right; left; reflexivity)) as F6.
  rewrite h_ule in F2, F3, F4, F5, F6. cbn [holds] in F1. change (uval rho (SVar 30)) with (bv_unsigned (rw rho V_TOP)) in *. unfold IMG_HI in *.
  rewrite !uval_lit in * by lia. pose proof (uval_range rho vF) as Rf. pose proof (uval_range rho (SVar gF)) as Rg.
  rewrite uval_add_litZ in F4 by lia.
  assert (E8 : uval rho (g8 gF) = (uval rho (SVar gF) * 8) mod 2 ^ 64).
  { unfold uval, g8. rewrite U_sll_lit. change (2 ^ (3 mod 64)) with 8. reflexivity. }
  apply (f_equal bv_unsigned) in F1. change (uval rho (g8 gF) = uval rho vF) in F1. rewrite E8 in F1.
  rewrite Z.mod_small in F1 by lia.
  constructor; [rewrite <- F1; rewrite Z.div_mul by lia; reflexivity | rewrite <- F1; apply Z_mod_mult | unfold IMG_HI; lia].
Qed.

Definition vb184 : sv := SAlu ALU_ADD vb (SLit 184).
Definition extra_tab : list (sv * sv * sv) := ltac2:(tb__ "0|3|
SeS10S10S1dS1dA2M0S1dA2M1S13G0S1dS13S1dS1dS106S1fZ0A1M2A4S1fZ8A1A4SeG1S13G0S1dS13S1dS1dS106S1fZ60A1A4S1fZ78A1A4SeG1S13G0S1dS13S1dS1dS106S1fZb8A1A4S1fZd8A1A4SeG1S13G0S1dS13S1dS1dSecG2A4S1fZ20A1A4SeG1S13G0S1dS13S1dS1dS108G2A4S1fZ30A1A4SeG1S13G0S1dS13S1dS1dS10cG2A4S10dA4S15G1A1A3A3A3A3A3A3").
Definition extraO (o : sobj) : bool := ltac2:(tb__ "0|3|
SfcS10S10S1dS1dA2M0S1dA2M1G1S1cS1cS32S34Vo;A1S18S1dS1dS18G0S1dR1A3M2A3A2S32S36Vo;A1S1aS1dS1dG2A3A2A2S32S35Vo;A1S1aG0S1dR1A3A2A2Lt;Sf1A3").
Definition extraX_tab : list (sv * sv) := ltac2:(tb__ "0|1|
SeS10S1dS1dA2M0S13S1dS1dS106S1fZ518A1A4SeG0S13S1dS1dS108S1fZ30A1A4SeG0S13S1dS1dS10cS10dA4SeG0S13S1dS1dSecS1fZ20A1A4SeG0S13S1dS1dS1fS132A1S1fZb8A1A4S15G0A1A3A3A3A3A3").
Definition extraX (r : sv * sv) : bool := existsb (xr_eqb r) extraX_tab.
Definition in_callers (rho : valuation) (a : Z) : Prop := ltac2:(tb__ "0|3|
S2S1S47S66Vrho;S106A2M0Va;A2S4aVa;S4bG0Z518A2A2A2S2S1S47S66Vrho;S108A2M1Va;A2S4aVa;S4bG1Z30A2A2A2S2S1S47S66Vrho;S10cA2M2Va;A2S4aVa;S4bG2S66Vrho;S10dA2A2A2A2S1S47S132Va;A2S4aVa;S4bS132Zb8A2A2A2A2A2A2").

Lemma obj_rangeZ : ltac2:(tb__ "0|2|
S20S21S3cS3cS3cS1S47S18S3cS3cS2eR5R4A2M0A3R3A2S4aR3S1aS3cS3cG0A3A2A2S0S3cS30R6S36R5A1A2R3A3S0S3cS30R7S35R6A1A2R3A3S1S47S4bS66R8S34R7A1A2M1R5A2R6A2S4aR6S4bG1R4A2A2A2F_;F_;F_;Fhi;Flo;Fa;Fo;Frho;").
Proof. intros rho o a lo hi Hr <- <-. unfold obj_range, obj_lo_of, obj_hi_of in Hr. unfold uval. exact Hr. Qed.

Lemma extraO_sound : ltac2:(tb__ "0|1|
S20S21S3cSe5R3A1S0S11SdfR3A1S12A3S1S47S18S3cS3cS2eR5R4A2M0A3R3A2S4aR3S1aS3cS3cG0A3A2A2Se8R6R4A2F_;F_;F_;Fa;Fo;Frho;").
Proof.
  intros rho o a [Bsp Bb Bal BL BB Btop] HE Hr. rewrite aceil_val in *. unfold IMG_HI in *.
  assert (E184 : uval rho vb184 = uval rho vb + 184) by (unfold vb184; apply uval_add_litZ; lia).
  unfold extraO in HE. apply existsb_exists in HE as (t & Hin & Heq).
  apply andb_prop in Heq as [Heq Hh]. apply andb_prop in Heq as [Hb Hl]. apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
  unfold in_callers. cbn [extra_tab In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd] in Hb, Hl, Hh;
    (eapply obj_rangeZ in Hr; [| rewrite Hl; first [apply soff_lit_small; lia | apply soff_smallu; lia] | rewrite Hh; first [apply soff_lit_small; lia | apply soff_smallu; lia]]);
    rewrite Hb in Hr; rewrite ?E184 in Hr; lia.
Qed.

Lemma extraX_sound : ltac2:(tb__ "0|1|
S20S10S1dS1dA2S3cSe5R3A1S0S11Se3R3A1S12A3S1S47S66R5S18S1dS1dR4A3A2M0R3A2S4aR3S4bG0S66R5S1aS1dS1dR4A3A2A2A2A2Se8R6R4A2F_;F_;F_;Fa;Fr;Frho;").
Proof.
  intros rho r a [Bsp Bb Bal BL BB Btop] HE Hr. rewrite aceil_val in *. unfold IMG_HI in *.
  assert (E184 : uval rho vb184 = uval rho vb + 184) by (unfold vb184; apply uval_add_litZ; lia).
  unfold extraX in HE. apply existsb_exists in HE as (t & Hin & Heq). apply xr_eqb_sound in Heq. subst t.
  unfold in_callers. cbn [extraX_tab In] in Hin. unfold pow10_tab in *.
  destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; destruct r as [b l]; injection E as <- <-; cbn [fst snd] in Hr;
    rewrite ?uval_lit in Hr by lia; rewrite ?E184 in Hr; lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S112S20SfS3fQ40A1A1S115OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S162S3eVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S3cS164VCST;R1A2S1S47Z0R2A2S4aR2S12eA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S3cS164VXGL;R1A2S1S47Z0R2A2S4aR2S12eA2A2F_;Fa;").

Hypothesis HXpow : ltac2:(tb__ "0|0|
S3cS1S47S132R1A2S4aR1S4bS132Zb8A2A2A2S164VXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
SfS10S10S3cS3cA2S3cA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 5 BX.
Let HNP : NP_okA NF := NP_okA_intro NF eq_refl.
Variable rho0 : valuation.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok.

Definition JLh (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S60VAInv;VCST;VXGL;VKc;SddVCST;VFB;VFF;A3VFB;VFF;VBX;S54Vnd;Aa").
Definition Posts_hvn : list (axst * jpostA) := ltac2:(tb__ "0|1|
SeS10S5Sf4A2M0S13S5Sf4S89S14dS90A1A4SeG0S13S5Sf4S88S14dS8fA1A4S15G0A1A3A3").

Definition PD_hvn : list (axst * ndesc) := ltac2:(tb__ "0|1|
SeS10S5S51A2M0S13S5S51S89S90A4SeG0S13S5S51S88S8fA4S15G0A1A3A3").

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S5fVAInv;VCST;VXGL;S65VKc;Vrho0;SddVCST;VFB;VFF;A3VFB;VFF;VBX;S54Vnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S10S5S51A2S128Fn;") := ltac2:(tb__ "0|0|
S63VAInv;VCST;VXGL;S65VKc;Vrho0;SddVCST;VFB;VFF;A3VFB;VFF;VBX;S54Ab").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
Sf6S3eS65Vrho0;Vtp0;S14cA5").

Lemma P0_now : ltac2:(tb__ "0|3|
S20S125S65Vrho0;R1A3SddVCST;VFB;VFF;Vrho0;A4S1S3cS1S47S66R4S10cA2M0R1A2S4aR1S4bG0S66R4S10dA2A2A2A2S13cVCST;Vrho0;VFB;VFF;R2A5F_;Fa;S1S151VFF;S66R3S106A2Z518A3S1S151VFF;S66R3S108A2Z30A3S1S3S0S3cS66R3S104A2Z0M1A3A1S3S0S3cS66R4S105A2G1A3A1F_;S0S14S145G1S101S10S10S3cS3cA2M2S3cA2G2S18G2S3cA2VFF;A4A2U0A3A2A2A2A2F_;F_;Frho;").
Proof.
  intros rho Hav (A & B & C & D & E). unfold uval, vL, vB, vb, vAL, vNK, vND. cbn [eval].
  rewrite <- (proj1 Hav 12%positive eq_refl), <- (proj1 Hav 15%positive eq_refl), <- (proj1 Hav 18%positive eq_refl),
          <- (proj1 Hav 58%positive eq_refl), <- (proj1 Hav 54%positive eq_refl), <- (proj1 Hav 56%positive eq_refl).
  repeat (split; [assumption|]). assumption.
Qed.

Lemma in_callers_ok : ltac2:(tb__ "0|0|
S20S3cSfS10S1dS1dA2A1SfS10S10S1dS3cA2S1dA2A1S125S65Vrho0;R4A3SddVCST;VFB;VFF;Vrho0;A4Se8R6R5A2S2S13cVCST;Vrho0;S137VFB;R7R5A3S13dVFF;R7R4A3R6A5S164VXGL;R6A2A2F_;F_;F_;Ffrs;Fkept;Fa;Frho;").
Proof.
  intros rho a kept frs Hav HP0 H. destruct (P0_now rho Hav HP0) as (HT & Hb & Hal & _ & _).
  destruct H as [H|[H|[H|H]]].
  - destruct Hb as (f & sz & fl & Hin & H1 & H2). left. right; right; right. exists f, sz, fl. split; [apply In_FFx; left; exact Hin | lia].
  - destruct Hal as (f & sz & fl & Hin & H1 & H2). left. right; right; right. exists f, sz, fl. split; [apply In_FFx; left; exact Hin | lia].
  - left. destruct (HT a H) as [P|[P|[(b0 & n0 & Hin & Hr)|(f & s0 & fl & Hin & Hr)]]]; [left; exact P | right; left; exact P | |].
    + right; right; left. exists b0, n0. split; [apply In_FBx; left; exact Hin | exact Hr].
    + right; right; right. exists f, s0, fl. split; [apply In_FFx; left; exact Hin | exact Hr].
  - right. exact (HXpow a H).
Qed.

Lemma extraO_client : ltac2:(tb__ "0|1|
S20S21S3cSfS10S1dS1dA2A1SfS10S10S1dS3cA2S1dA2A1Se5R5A1S125S65Vrho0;R6A3SddVCST;VFB;VFF;Vrho0;A4S0S11SdfR7A1S12A3S1S47S18S3cS3cS2eR9R8A2M0A3R7A2S4aR7S1aS3cS3cG0A3A2A2S13cVCST;Vrho0;S137VFB;RaR7A3S13dVFF;RaR6A3R8A5F_;F_;F_;F_;F_;Ffrs;Fkept;Fa;Fo;Frho;").
Proof.
  intros rho o a kept frs BZ Hav HP0 HE Hr. destruct (P0_now rho Hav HP0) as (HT & Hb & Hal & _ & _).
  pose proof BZ as [Bsp Bb Bal BL BB Btop]. rewrite aceil_val in *. unfold IMG_HI in *.
  assert (E184 : uval rho vb184 = uval rho vb + 184) by (unfold vb184; apply uval_add_litZ; lia).
  unfold extraO in HE. apply existsb_exists in HE as (t & Hin & Heq).
  apply andb_prop in Heq as [Heq Hh]. apply andb_prop in Heq as [Hb0 Hl]. apply sv_eqb_sound in Hb0. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
  cbn [extra_tab In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd] in Hb0, Hl, Hh;
    (eapply obj_rangeZ in Hr; [| rewrite Hl; first [apply soff_lit_small; lia | apply soff_smallu; lia] | rewrite Hh; first [apply soff_lit_small; lia | apply soff_smallu; lia]]);
    rewrite Hb0 in Hr; rewrite ?E184 in Hr.
  1-4: destruct Hb as (f & sz & fl & Hin & H1 & H2); right; right; right; exists f, sz, fl; split; [apply In_FFx; left; exact Hin | lia].
  - destruct Hal as (f & sz & fl & Hin & H1 & H2). right; right; right. exists f, sz, fl. split; [apply In_FFx; left; exact Hin | lia].
  - destruct (HT a ltac:(lia)) as [P|[P|[(b0 & n0 & Hin & Hr')|(f & s0 & fl & Hin & Hr')]]]; [left; exact P | right; left; exact P | |].
    + right; right; left. exists b0, n0. split; [apply In_FBx; left; exact Hin | exact Hr'].
    + right; right; right. exists f, s0, fl. split; [apply In_FFx; left; exact Hin | exact Hr'].
Qed.

Lemma siteP : ltac2:(tb__ "0|0|
S112S20SfS1eA1SfS10S1dS1dA2A1SfS10S10S1dS3cA2S1dA2A1S17S14A1SfS21A1S20SfS3fQ40A1A1S115VAInv;RaR3R2R1A4S100S1eS28RaA1R9A3S0S11SdeRaA1S12A3S125S65Vrho0;RcA3SddVCST;VFB;VFF;Vrho0;A4S56Vrho0;RfA2S136RfS114S113R10A1A1A2S5bVFB;R11A2S5cVFF;R12A2S59VFB;R13R12R10A4S138R13R11A2S139R14R12A2S58VFF;R16R15R12A4S0S11S168R15R14R13R12SdfR11A6S12A3S149VCST;R18S19S3cA1R17R12A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr skip R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR Hchk.
  eapply (robjsP_okA segs AInv CST ALA rho0 FB FF Ai rho facts tv fr skip extraO R rho1 tp1 md1 HM HF HT HTK HBf HFF HN HD HZ HFR Hchk).
  intros o a Ho HE Hr. exact (extraO_client rho o a _ _ (basez_of rho facts HF HB) Hav HP0 HE Hr).
Qed.
Lemma siteF : ltac2:(tb__ "0|0|
S112S20SfS1eA1SfS10S1dS1dA2A1SfS10S10S1dS3cA2S1dA2A1SfS21A1S20SfS3fQ40A1A1S115VAInv;R9R3R2R1A4S100S1eS28R9A1R8A3S0S11SdeR9A1S12A3S125S65Vrho0;RbA3SddVCST;VFB;VFF;Vrho0;A4S56Vrho0;ReA2S136ReS114S113RfA1A1A2S59VFB;R10RfRdA4S138R10ReA2S139R11RfA2S58VFF;R13R12RfA4S0S11S153R12R11R10S19S14A1SdfRfA6S12A3S173VCST;Vrho0;VFB;VFF;R14R12R11R10A8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR Hchk.
  eapply (robjsP_okF segs AInv CST ALA rho0 FB FF Ai rho facts tv fr extraO R rho1 tp1 md1 HM HF HT HTK HN HD HZ HFR Hchk).
  intros o a Ho HE Hr. exact (extraO_client rho o a _ _ (basez_of rho facts HF HB) Hav HP0 HE Hr).
Qed.
Lemma siteH : ltac2:(tb__ "0|1|
S112S20SfS1eA1SfS10S1dS1dA2A1SfS10S10S1dS3cA2S1dA2A1SfS21A1S20SfS3fQ40A1A1S115VAInv;R9R3R2R1A4S100S1eS28R9A1R8A3S0S11SdeR9A1S12A3S125S65Vrho0;RbA3SddVCST;VFB;VFF;Vrho0;A4S56Vrho0;ReA2S136ReS114S113RfA1A1A2S59VFB;R10RfRdA4S138R10ReA2S139R11RfA2S58VFF;R13R12RfA4S0S11S153R12R11R10S19S14A1SdfRfA6S12A3S21S3cSfdS21R2R12A3S1S47S18S3cS3cS2eR17R3A2M0A3R2A2S4aR2S1aS3cS3cG0A3A2A2S2S13cVCST;Vrho0;S137VFB;R18R16A3S13dVFF;R18R15A3R3A5S2S1S47Z0R3A2S4aR3S12eA2A2S146R3A1A2A2F_;F_;Fa;Fo;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR Hchk.
  eapply (robjsP_hse segs AInv CST ALA rho0 FB FF Ai rho facts tv fr extraO R rho1 tp1 md1 HM HF HT HTK HN HD HZ HFR Hchk).
  intros o a Ho HE Hr. exact (extraO_client rho o a _ _ (basez_of rho facts HF HB) Hav HP0 HE Hr).
Qed.
Lemma siteX : ltac2:(tb__ "0|4|
S112S20SfS1eA1SfS10S1dS1dA2A1M0SfS10S10S1dS3cA2S1dA2M1A1M2S17S14A1M3SfS21A1G0S20SfS3fQ40A1A1S115VAInv;RbR3R2R1A4S100S1eS28RbA1RaA3S0S11SdeRbA1S12A3S125S65Vrho0;RdA3SddVCST;VFB;VFF;Vrho0;A4S56Vrho0;R10A2S136R10S114S113R11A1A1A2S5bVFB;R12A2S5cVFF;R13A2S59VFB;R14R13R11A4S138R14R12A2S139R15R13A2S58VFF;R17R16R13A4S0S11S152VXGL;R16R15R14R13R12Se3R11A8S12A3S1S143VCST;VXGL;Vrho0;VFB;VFF;R18R16G3G2Lskip;R14S14S13bG1R1R16A3Li;R15X17x2R12A9S1S14bVCST;VXGL;R19S19S3cA1R18R12A6S174R18R12A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FX;Fobjs;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr skip objs X rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR Hchk.
  assert (HEX : forall r a, In r X -> extraX r = true -> uval rho (fst r) <= a < uval rho (fst r) + uval rho (snd r) ->
            pclMA CST rho0 (FBx FB rho tv) (FFx FF rho (match skip with Some i => remove_nth i fr | None => fr end)) a \/ RtCells.in_rangesZ XGL a).
  { intros r a Hr HE Ha. apply (in_callers_ok rho a _ _ Hav HP0). exact (extraX_sound rho r a (basez_of rho facts HF HB) HE Ha). }
  split; [exact (xrs_checkL_sound segs AInv CST XGL ALA rho0 FB FF Ai rho facts tv fr skip objs extraX X rho1 tp1 md1 HM HF (T_ok_T0 rho0 _ Ai HT HTK) HN HD HZ HFR Hchk HEX)|].
  exact (xrs_checkL_okA segs AInv CST XGL ALA HCST HXGL rho0 FB FF Ai rho facts tv fr skip objs extraX X rho1 tp1 md1 HM HF HT HTK HBf HFF HN HD HZ HFR Hchk HEX).
Qed.

Lemma slot_holds : ltac2:(tb__ "0|1|
S20SfS1eA1S1dS100S1eS28R3A1R2A3S0S11SfcS1eS29S22S26SdbS107S1fZ3A1A3R2A2A1R3A3S12A3S0S11SfcS1eS29S22R3S1fS119A1M0A2A1R4A3S12A3S0S11SfcS1eS29S22S107S104A2A1R5A3S12A3S0S11SfcS1eS29S22S104G0A2A1R6A3S12A3S0S11SfcS1eS29S22S10aR6A1G0A2A1R7A3S12A3S100S1eS28R9A1S93R7A1A3F_;F_;F_;F_;F_;F_;Fk;FF;Frho;").
Proof.
  intros rho F k HF H1 H2 H3 H4 H5.
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3.
  pose proof (holds_mem _ _ _ HF H4) as F4. pose proof (holds_mem _ _ _ HF H5) as F5.
  rewrite h_ule in F1, F2, F3, F4, F5. unfold B32 in *. rewrite uval_lit in F2 by lia. rewrite uval_lit in F4 by lia. rewrite uval_lit in F5 by lia.
  pose proof (uval_range rho vNC) as RC. pose proof (uval_range rho k) as Rk. pose proof (uval_range rho vNK) as RK.
  rewrite uval_add_litZ in F1 by lia.
  assert (E4k : uval rho (kb4 k) = 4 * uval rho k) by (unfold kb4; apply uval_mul_lit; lia). rewrite E4k in F5.
  assert (E4c : uval rho (cb4 vNC) = 4 * uval rho vNC) by (unfold cb4; rewrite uval_mul_comm; apply uval_mul_lit; lia).
  unfold slot_facts. change (SMd M_MUL vNC (SLit 4)) with (cb4 vNC).
  constructor; [|constructor; [|constructor; [|constructor]]]; rewrite h_ule.
  - rewrite uval_add_litZ by (rewrite ?E4c; lia). rewrite E4c, E4k. lia.
  - rewrite E4c, E4k. lia.
  - unfold B32. rewrite E4c, uval_lit by lia. lia.
Qed.

Lemma payA_same : ltac2:(tb__ "0|1|
SfS1eA1SfS67A1S0S11S69R1A1S12A3S148S65Vrho0;SddVCST;VFB;VFF;A3R3S1fZ0M0A1G0R2R2A8F_;Fbd;Ffacts;").
Proof.
  intros facts bd Hw. split; [exact Hw|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem. rewrite uval_lit by lia.
  split; [lia|]. split; [lia | exact Hn].
Qed.

Lemma frozen_stableA' : ltac2:(tb__ "0|0|
S3dS3dS51S20S16aS65R3A2S0S11S55R4R3A2S12A3S50S3eR6S62VAInv;VCST;VXGL;S65VKc;Vrho0;SddVCST;VFB;VFF;A3VFB;VFF;VBX;S54R4R3AdA3F_;F_;Frho;Fnd;Fm;Fn;").
Proof.
  intros n m nd rho Hm Hb r r' tp tr md md' _ Hme (Ai & kc & HJ). exists Ai, kc.
  eapply (JAi_stable segs AInv CST XGL NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue HKc ALA m nd Ai kc rho rho tp tr md md'); [exact Hm | exact Hb | apply agree_below_refl | exact Hme | exact HJ].
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S3cSfS3fQ40A1A1S129F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S4eS5S20SfS3fQ40A1A1S129S100S1eS28R3A1S23S6R4A1A1A3VTR;S4dS3eR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S129S129S129S12aR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S4eS4eS5S5S135SfS21A1M0SfS10S5Sf4A2M1A1SfS10S1dS1dA2M2A1S129S20SfS3fQ40A1A1M3G2SfdG2R1R5A3SfdG2R2S7RbA1A3F_;Fr;S0S17G0A1Sf8RaR9R8A3S16G0R7A2A3S0S11SfaRbRaR9R8S101G1S5S18S5Sf4A2R7A4A5S12A3S20G3VTR;S4dS3eRfRdR2R1A5Sf6S3eS25S6RdA1A1R2R1RaA5A2Ftp1;Frho1;SfS116A1M4S131S115S4fS3eR9R8R10S13G4S165R3S166R2R1A2A4A5R13RaR9R4R2A4R13S134S133RbRfS12dR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S5Sf4G4S131S115S20G3G4S131S115SfdG1S13S5Sf4RaR9A4R14A3S4fS3eR12R11R19S13G4S165R9S166R8R7A2A4A5R1cR13R12RaR8A4S125S25S6R1aA1A1S134S133R14R18S12dR9R13RaA3A3R19A2R8A3S4fS3eR9R8ReS13G4S165R7S166R6R5A2A4A5ReS134S133R16R1aS12dRbR15RcA3A3R1bA2R15RaR9R8R6A6S1S171R17S12dRcR16RdA3R1bR1cR1dR10R1eR19RbA9S20S126R18S12dRdR17ReA3R1cR1dS6R1eA1S6R1fA1S6R11A1R1RcA9VTR;S4dS3eSfbR11S134S133R19R1dS12dReR18RfA3A3R1eA2R18RdRcA5S172R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S4dS3eR11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CVRES : ltac2:(tb__ "0|1|
SfS10S3cS3cA2M0A1SfS10G0S3cA2A1S6cS20SfS3fQ40A1A1S6aZ3R3A2VTR;S4dS3eS5aVAInv;VCST;VXGL;VKc;S167R6R5A2R6R5R4S54S120AaS117R3R2A5Sf6S3eS65R3R2S13fVAInv;VCST;VXGL;VKc;S167S54SeeR6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CSM : ltac2:(tb__ "0|2|
S112S20SfS3fQ40A1A1VTR;S4dS3eS15dVAInv;Z0M0R3VKc;A4Sc1R2R1A5Sf6S3eS65R2R1SeS10S5Sf4A2M1S13S5Sf4Sc0S15aVAInv;VCST;VXGL;G0R3VKc;A6A4S15G1A1A3A5A2Ftp1;Frho1;FAi;").

Hypothesis CMEMSET : ltac2:(tb__ "0|1|
S112S20SfS3fQ40A1A1VTR;S4dS3eS15cVAInv;R3VKc;A3S9aR2R1A5Sf6S3eS65R2R1SeS10S5Sf4A2M0S13S5Sf4S98S159VAInv;VCST;VXGL;R3VKc;A5A4S15G0A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CMEMCPY : ltac2:(tb__ "0|2|
S112S20SfS3fQ40A1A1VTR;S4dS3eS15bVAInv;R3VKc;A3S77R2R1A5Sf6S3eS65R2R1SeS10S5Sf4A2M0S13S5Sf4S76S159VAInv;VCST;VXGL;R3VKc;A5A4M1SeG0G1S15G0A1A3A3A5A2Ftp1;Frho1;FAi;").

Hypothesis CALL_sd : ltac2:(tb__ "0|2|
S5S135SfS21A1M0S20SfS3fQ40A1A1S51S129S0S17G0A1Sf8R7S10bR6A3S16G0R5A2A3S0S11Sf9R8S10bR7R6S101S9S5SbS110A4A5S12A3S0S11S169S65S25S6R9A1A1A2S12A3S0S11S55S25S6RaA1A1R5A2S12A3S0S11SffS1eS37S25S6RbA1M1A1A1S23G1A1A3S12A3S9S20SfdS9R2S110A3S3aS25S6RfA1A1RcR2A3VTR;S4dS3eVJAv;RbA1S127S23S6R10A1A1Sf5RfS10bSbR4A1R10ReA5A2R3RcA5RaA2F_;F_;Frho';FL;VTR;S4dS3eVJAv;R8A1RdRaR9A5R7A2F_;F_;F_;F_;F_;F_;FQ;Fnd;Ftp;Frho;FR;Fs;FCl;").
Hypothesis REENTER : ltac2:(tb__ "0|4|
S5S51S10S3cS1dA2M0S20SfS3fQ40A1A1M1S3cG1SfdS10S10S5S51A2M2G0A2S13G2G0S13S5S51R7R6A4R5A4S72A3S1S47Z0S5eS13G2G0S13S5S51R8R7A4R6A4R5A2M3A2S4aG3R3A2A2VTR;S4dS3eVJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S5S51S20SfS3fQ40A1A1M0S3cG0SfdS10S5Sf4A2S13S5Sf4R6S14dR5A1A4S14cA3VTR;S4dS3eVJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Ltac meas := unfold emeasA; cbn [eda_rank eda_var fst snd z0 eval]; rewrite lit_unsigned; cbn; lia.

Ltac vmr := first [ lazymatch goal with |- @eq ?T ?t ?v => tryif first [ has_evar t | has_evar v ] then fail else vm_cast_no_check (@eq_refl T v) end
                  | vm_compute; reflexivity ].
Tactic Notation "innth" integer(n) := cbn [In cutsH exitsH Posts_hvn PD_hvn PD_vr]; do n right; left; reflexivity.

Lemma shobj_range_hse : ltac2:(tb__ "0|1|
S20SfS1eA1S3cS100S1eS28R3A1R2A3S0S11Se0R3A1S12A3S1S47S18S3cS3cS2eR5S154S70Z0Z8S15S2aA1S2bA5A2M0A3R3A2S4aR3S1aS3cS3cG0A3A2A2S146R4A1F_;F_;F_;Fa;FF;Frho;").
Proof.
  intros rho F a HF HFR Hr. pose proof (framez_of rho F HF HFR) as [G1 G2 G3]. unfold is_shadowZ, IMG_HI in *.
  unfold shobj, obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  unfold SHADOW_OFF, HIGH_SHADOW_END in *. rewrite !soff_lit_small in Hr by lia.
  change (bv_unsigned (eval rho (SVar gF))) with (uval rho (SVar gF)) in Hr. rewrite G1 in Hr.
  pose proof (uval_range rho vF). lia.
Qed.

Lemma X_Y_ep : ltac2:(tb__ "0|6|
S5S5SfS10S1dS1dA2A1SfS67A1S1dS1dS20SfS3fQ40A1A1M0S3cG0S0S1dSdRaA1S1fS130A1A3S0S11ScSeS1eS31SaS70A1S6eA2SeS1eS22S24S70A1S1fS4cS48Z2M1Z3dA2Z1A2A1A2S15S1eA1A3A3S23S6RbA1A1A2S12A3S0S11S141S8cR8R7A2S7RcA1A2S12A3S0S11S38S6S157RdS8cR9R8A2S70Z0Z8A5A1A1S12A3S0S11S38S6S78ReRaR9A3A1A1S12A3S0S11S55S25S6RfA1A1S53RdS6dRcS52A4A2S12A3S0S11SdeS23S6R10A1A1A1S12A3S0S11Se0S23S6R11A1A1A1S12A3S0S11S153S23S6R12A1M2A1R10S6dS19S14A1SdfS27G2A1A6S12A3S0S11S152VXGL;S23S6R13A1M3A1R11S6dS16S14U0A2S27G3A1Se3S8cRfReA2A8S12A3S0S5S78R14R10RfA3R13A3SfdS10S10S5S51A2M4S10S3cS1dA2M5A2S13G4G5S13S5S51R14S53R13S6dR12S52A4A4S13S3cS1dZ32S118A4A4S72A3S47S49Z37S48G1Z40A2A2ReA2VTR;S4dS3eVJAv;S53R15S6dR14S52A4A1R17R11R10A5VFAM;RfReA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fk;Fd;Fbd;Ftv;FC;FY;").
Proof.
  intros Y C tv bd d k rho tp b tp0 Hbase Hfe HXi Hwf1 Hwf2 Hnb HB HFRF HRO HXL HC HinC Hb.
  eapply TR_pre; [|apply (REENTER C (NDA tv fr_hvn bd ANone) (50, z0)); [exact HinC | meas]].
  intros w Hw. rewrite <- HC. unfold epi_state.
  apply (JA_flag_carve segs HTOP AInv CST XGL ALA HCST HXGL LFLAG NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hvn bd ANone 0%nat 110%positive 0 120%positive (shadow_reopen_stateA Y (X_epi d k) gF 0 8) rho tp w eq_refl ltac:(lia)).
  - exact Hbase.
  - exact Hwf2.
  - intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. cbn [shadow_reopen_stateA ax_S ss_facts ss_objs ax_X] in HF |- *. split.
    + intros o a Ho Hr. apply in_app_or in Ho as [Ho|[<-|[]]].
      * exact (siteH Ai rho _ tv fr_hvn _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO o a Ho Hr).
      * right. right. exact (shobj_range_hse rho _ a HF HFRF Hr).
    + exact (proj2 (proj2 (siteX Ai rho _ tv fr_hvn (Some 0%nat) _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL))).
  - apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue HKc HBX HNP
             tv fr_hvn bd ANone 0%nat 110%positive 0 120%positive gF 0 8 Y (X_epi d k) rho tp w eq_refl ltac:(lia) Hbase ltac:(lia)
             ltac:(vm_compute; split; [discriminate|discriminate]) Hfe (xrs_inclb_sound _ _ HXi) Hwf1); [|exact Hw].
    intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
    + exact (siteF Ai rho _ tv fr_hvn _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO).
    + intros r y Hr Hy. left. exact (proj1 (siteX Ai rho _ tv fr_hvn (Some 0%nat) _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL) r y Hr Hy).
Qed.

Lemma XH_X_epf0 : ltac2:(tb__ "0|1|
S20SfS3fQ40A1A1M0S3cG0S47S49Z37S48Z2Z40A2A2R2A2VTR;S4dS3eVJAv;S81A1Sa0R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. eapply TR_pre; [intros w Hw; exact (SPA_axforms segs _ xf_cf rho X_epf0 Y_epf0 tp w Y_epf0_eq Hw)|].
  apply (X_Y_ep Y_epf0 C_epf0 _ _ vND vNK rho tp b tp0); [vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_epf0_eq | innth 18 | exact Hb].
Qed.
Lemma XH_X_epf1 : ltac2:(tb__ "0|1|
S20SfS3fQ40A1A1M0S3cG0S47S49Z37S48Z2Z40A2A2R2A2VTR;S4dS3eVJAv;S81A1Sa1R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. eapply TR_pre; [intros w Hw; exact (SPA_axforms segs _ xf_cf rho X_epf1 Y_epf1 tp w Y_epf1_eq Hw)|].
  apply (X_Y_ep Y_epf1 C_epf1 _ _ vND vNK rho tp b tp0); [vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_epf1_eq | innth 19 | exact Hb].
Qed.

Lemma cm_rng : ltac2:(tb__ "0|4|
S20SfS1eA1S1dS100S1eS28R3A1R2A3S0S11Se0R3A1S12A3S0S11SfcS1eS29S22R3S24P1eA1A2A1R4A3S12A3S0S11SfcS1eS29S22S109S107A1M0S1fS119A1A2A1R5A3S12A3S1S0S3cS66R7S26SdbR5G0A3A2S4bS66R7R5A2S66R7G0A2M1A2A3S1S0S3cS30R7G0A2G1A3S1S0S3cS30R7S26SdbG0S1fZcM2A1A3A2S4bG1G2A2A3S0S3cS66R7S26SdbS6eS1fZ20M3A1A3A2S4bS66R7S6eA2G3A2A3A2A2A2F_;F_;F_;F_;Fd;FF;Fr;").
Proof.
  intros r F d HF HFR Hd Hs. pose proof (framez_of r F HF HFR) as [_ _ G3]. unfold IMG_HI in G3.
  pose proof (holds_mem _ _ _ HF Hd) as F1. pose proof (holds_mem _ _ _ HF Hs) as F2.
  rewrite h_ule in F1, F2. change (uval r (SVar 30)) with (bv_unsigned (rw r V_TOP)) in F1. unfold B32 in F2. rewrite uval_lit in F2 by lia.
  pose proof (uval_range r (cb4 vNC)) as Rc. pose proof (uval_range r d) as Rd. pose proof (uval_range r vF) as Rf.
  assert (A12 : uval r (SAlu ALU_ADD (cb4 vNC) (SLit 12)) = uval r (cb4 vNC) + 12) by (apply uval_add_litZ; lia).
  split; [apply uval_add_small; lia|]. split; [apply soff_smallu; lia|]. split; [rewrite <- A12; apply soff_smallu; rewrite A12; lia|].
  apply uval_add_litZ; lia.
Qed.

Lemma X_E_sd : ltac2:(tb__ "0|7|
S5S5S5S5SfS41A1S135SfS21A1M0S20SfS3fQ40A1A1M1S3cG1S3cS0S17S5A1S42RcR8A2S16S5RbA2A3S0S17G0A1Sf8RcS10bR8A3S16G0R7A2A3S0S11Sf9RdS10bR9R8S101S9S5SbS110A4A5S12A3S0S11S169S65S25S6ReA1A1A2S12A3S0S11S55S25S6RfA1A1S73A2S12A3S0S11SffS1eS37S25S6R10A1M2A1A1S23G2A1A3S12A3S0S5S127S23S6R11A1A1Sf5RdS10bS10eR11RcA5A2R10A3S0S5S127S23S6R12A1A1Sf5ReS10bS10fR12RdA5A2R10A3SfdS10S10S5S51A2M3S10S3cS1dA2M4A2M5S13G3G4S13S5S51R12S73A4M6S13S3cS1dR9S118A4A4S72A3SfdG5S13G3G4G6S13S3cS1dRaS118A4A4S72A3S47Z0RbA2S47S49S4bRcZ1A2S48Z2Z40A2A2ReA2VTR;S4dS3eVJAv;S73A1R18R11R10A5VFAM;RfReA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frk;Ftp0;Fb;Ftp;Frho;FR;Fs;Fxf;FT1;FT0;FE;FE0;").
Proof.
  intros E0 E T0 T1 xf s R rho tp b tp0 rk HE He Hchk Hnf Hnb Hfb HT0 HT1 Hin0 Hin1 Hrk Hb.
  eapply TR_pre; [intros w Hw; exact (SPA_axforms segs _ xf rho E0 E tp w HE Hw)|].
  apply (CALL_sd E s R rho tp ndp (FAM b tp0) He Hchk Hnf Hnb Hfb).
  intros L rho' HL Hag. cbn [Posts_sd In] in HL. destruct HL as [<-|[<-|[]]]; cbn [la_state].
  - rewrite HT0. apply (REENTER T0 ndp (rk, z0)); [exact Hin0|]. unfold emeasA. cbn [eda_rank eda_var fst snd z0 eval]. rewrite lit_unsigned by lia. lia.
  - rewrite HT1. apply (REENTER T1 ndp (rk, z0)); [exact Hin1|]. unfold emeasA. cbn [eda_rank eda_var fst snd z0 eval]. rewrite lit_unsigned by lia. lia.
Qed.
Lemma XH_E_A : ltac2:(tb__ "0|1|
S20SfS3fQ40A1A1M0S3cG0S47S49Z5aS48Z2Z40A2A2R2A2VTR;S4dS3eVJAv;S73A1S95R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_E_sd E_A0 E_A T_A0 T_A1 xf_sd s_A R_A rho tp b tp0 88 E_A_eq);
    [vmr|vmr|vmr|vmr|vmr| exact T_A0_eq | exact T_A1_eq | innth 3 | innth 4 | lia | lia].
Qed.
Lemma XH_E_B : ltac2:(tb__ "0|1|
S20SfS3fQ40A1A1M0S3cG0S47S49Z56S48Z2Z40A2A2R2A2VTR;S4dS3eVJAv;S73A1S74R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_E_sd E_B E_B T_B0 T_B1 [] s_B R_B rho tp b tp0 84 E_B_eq);
    [vmr|vmr|vmr|vmr|vmr| exact T_B0_eq | exact T_B1_eq | innth 5 | innth 6 | lia | lia].
Qed.
Lemma XH_E_C : ltac2:(tb__ "0|1|
S20SfS3fQ40A1A1M0S3cG0S47S49Z52S48Z2Z40A2A2R2A2VTR;S4dS3eVJAv;S73A1S75R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_E_sd E_C E_C T_C0 T_C1 [] s_C R_C rho tp b tp0 80 E_C_eq);
    [vmr|vmr|vmr|vmr|vmr| exact T_C0_eq | exact T_C1_eq | innth 7 | innth 8 | lia | lia].
Qed.

Lemma HIN_v : ltac2:(tb__ "0|1|
S20S131S112S20SfS3fQ40A1A1S115S100S1eS28R6A1S23S6S6fA1A1A3SddVCST;VFB;VFF;Vrho0;A4S125S65Vrho0;R8A3VAInv;R7R6R5R4A4S56Vrho0;R8A2S136RbS114S113R9A1A1A2S5bVFB;RaA2S5cVFF;RbA2S58VFF;RcReS6dA4S1S140VCST;Vrho0;VFB;VFF;RfS15S10S1dS1dA2A1M0S6dS7aA8S1S142VCST;VXGL;Vrho0;VFB;VFF;RfG0S6dS80A9S167S137VFB;RfG0A3S13dVFF;RfS6dA3S134S133RfS7aReA3S71A2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HTP HTK HBf HFF HFR. destruct (P0_now rho Hav HP0) as (HT & Hb & Hal & HKD & _).
  assert (HB : baseF (ss_facts (ax_S E_vr)) = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof (basez_of rho _ HF HB) as BZ. pose proof BZ as [Bsp Bb Bal BL BB Btop]. rewrite aceil_val in *.
  assert (HN0 : tvinA FB Ai rho []) by constructor. assert (HZ0 : tvz rho []) by constructor.
  split; [|split].
  - intros o a Ho Hr. eapply (robjs_checkP_sound segs AInv CST ALA rho0 FB FF Ai rho _ [] fr_hvn None extraO R_v rho1 tp1 md1 HM HF (T_ok_T0 rho0 _ Ai HTP HTK) HN0 I HZ0 HFR ltac:(vmr));
      [intros o' a' Ho' HE Hr'; exact (extraO_client rho o' a' _ _ BZ Hav HP0 HE Hr') | exact Ho | exact Hr].
  - exact (proj1 (siteX Ai rho _ [] fr_hvn None (ss_objs (ax_S E_vr)) Xk_v rho1 tp1 md1 HM HF HB Hav HP0 HTP HTK HBf HFF HN0 I HZ0 HFR ltac:(vmr))).
  - unfold P0_vr. rewrite !rw_call'.
    change (wsub_get s_v 17) with vNK. change (wsub_get s_v 15) with vND. change (wsub_get s_v 14) with vAL. change (wsub_get s_v 12) with vb184.
    split; [exact HKD|]. split.
    + destruct Hb as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [apply In_FFx; left; exact Hin|].
      assert (E184 : uval rho vb184 = uval rho vb + 184) by (unfold vb184; apply uval_add_litZ; unfold IMG_HI in *; lia).
      unfold uval in E184, H1, H2. rewrite E184. lia.
    + destruct Hal as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [apply In_FFx; left; exact Hin|]. unfold uval in H1, H2. lia.
Qed.

Lemma XH_E_vr : ltac2:(tb__ "0|1|
S20SfS3fQ40A1A1M0S3cG0S47S49Z4aS48Z2Z40A2A2R2A2VTR;S4dS3eVJAv;S73A1S97R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  eapply TR_pre with (P := SPA segs (JAv ndp) E_vr rho tp).
  { intros w Hw. exact (SPA_axforms segs _ xf_vr rho E_vr0 E_vr tp w E_vr_eq Hw). }
  apply TR_facts. intros HF. unfold ndp, ndF. change (tv_hvn vND vNK) with ([] ++ tv_hvn vND vNK).
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue HKc HBX P0_vr PTrue (fun _ H => H) (fun _ _ _ H => H)
           Pre_vr Lib_vec_reserve.nd0 PD_vr NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CVRES eq_refl
           E_vr s_v R_v Xk_v rho tp [] (tv_hvn vND vNK) fr_hvn (bd_hvn vNC vNK) [] ANone (FAM b tp0)).
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - apply payA_of_bud_pay. vmr.
  - vmr.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK. exact (HIN_v rho ms Ai rho1 tp1 md1 HF' HP0 Hav HM HT HTK HBf HFF HFR).
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [PD_vr In] in Hd. destruct Hd as [Hd|[Hd|[Hd|[]]]]; injection Hd as <- <-;
      cbn [fst snd nd_tv nd_bd nd_am Lib_vec_reserve.nd0 ND am_subst app].
    +
      rewrite T_keep0_eq, imp_keep_tv, imp_keep_bd. rewrite app_nil_r.
      eapply TR_pre; [|apply (REENTER T_keep ndk (70, z0)); [innth 10 | meas]].
      intros w Hw. rewrite <- T_keep_eq. apply (SPA_refacts_JA segs); [exact Hw | vmr |].
      intros tr md HJ HF2. apply Forall_app. split; [|exact HF2]. apply Forall_app. split.
      * apply (slot_holds rho' _ vNK HF2); vmr.
      * assert (TNZ : tnz rho' (vND, kb4 vNK)).
        { destruct HJ as (Ai & kc & Hav' & _ & _ & _ & _ & _ & _ & _ & _ & HP0' & _). destruct (P0_now rho' Hav' HP0') as (_ & _ & _ & HKD & _).
          pose proof (holds_mem _ _ (SPUle (SAlu ALU_ADD vNC (SLit 3)) vNK) HF2 ltac:(vmr)) as F1.
          pose proof (holds_mem _ _ (SPUle vNC vNK) HF2 ltac:(vmr)) as F3. pose proof (holds_mem _ _ (SPUle vNK (SLit B32)) HF2 ltac:(vmr)) as F4.
          rewrite h_ule in F1, F3, F4. unfold B32 in F4. rewrite uval_lit in F4 by lia. pose proof (uval_range rho' vNC).
          rewrite uval_add_litZ in F1 by lia. unfold tnz. cbn [fst]. apply HKD. lia. }
        pose proof (JA_tv_facts segs AInv CST XGL NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue ALA _ _ _ _ _ (vND, kb4 vNK) eq_refl HJ (or_introl eq_refl) TNZ) as TF.
        constructor; [|constructor]. apply (proj1 (Forall_forall _ _) TF). unfold tv_factsA. cbn [fst snd]. do 5 right. left. reflexivity.
    +
      rewrite T_fail0_eq, imp_fail_tv. change (bd_subst _ []) with (@nil bitem). cbn [app].
      apply (REENTER T_fail0 ndf (70, z0)); [innth 12 | meas].
    +
      rewrite T_grown0_eq, imp_grown_tv, imp_grown_bd. rewrite app_nil_r.
      eapply TR_pre; [|apply (REENTER T_grown ndg (70, z0)); [innth 11 | meas]].
      intros w Hw. rewrite <- T_grown_eq. apply (SPA_refacts_JA segs); [exact Hw | vmr |].
      intros tr md _ HF2. apply Forall_app. split; [|exact HF2]. apply (slot_holds rho' _ vKg HF2); vmr.
Qed.

Lemma site_pure : ltac2:(tb__ "0|2|
S5S135SfS21A1S20SfS10S1dS1dA2A1SfS67A1S0S11SdeS23S6R6A1A1A1S12A3S0S11S168S23S6R7A1A1R3S6dS19S14A1M0SdfR5A6S12A3S0S11S152VXGL;S23S6R8A1M1A1R4S6dG0S27G1A1Se3S7R8A1A8S12A3S14aVAInv;VCST;VXGL;S65Vrho0;SddVCST;VFB;VFF;A3VFB;VFF;R9R8R7R6S53R5S6dR4S52A4S19S3cA1S112S131S4L_;L_;AfF_;F_;F_;Fbd;Ftv;Frho;FR;Fs;FE;").
Proof.
  intros E s R rho tv bd HB HR HX Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK. cbn [nd_tv nd_fr] in HN, HD, HZ, HFR.
  split; [exact (siteP Ai rho _ tv fr_hvn None R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HR)|].
  split; [exact (proj1 (proj2 (siteX Ai rho _ tv fr_hvn None _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HX))) | exact I].
Qed.

Lemma X_E_mc : ltac2:(tb__ "0|9|
S5S5S5S5S1dS1dSfS10S1dS1dA2A1SfS67A1S135SfS21A1M0S20SfS3fQ40A1A1M1S3cG1S0S17S5A1S42ReS84A2S16S5RdA2A3S0S17S21A1M2SfeS21S27S6ReA1A1U4A3S16S21S2cRbS109S107A1M3S26SdbG3S1fZcA1A3S15S2aA1M4S2bA5A2A3S0S11S2fS25S6RfA1A1SafRcA1A2S12A3S0G2SfeS21S27S6Se1R10RdA2A1A1UcA3S16S21S2cS6eS1fZ20A1S1fZ2cA1G4S2bA5A2A3S0S11S2fS25S6Se1R11ReA2A1A1Sb5A2S12A3S0S11Se0S23S6R12A1A1A1S12A3S0S11SfcS1eS29S22R10S24P1eA1A2A1S23S6R13A1A1A3S12A3S0S11SfcS1eS29S22G3S1fS119A1A2A1S23S6R14A1A1A3S12A3S0S5Se6Se1R15R12A2A1R14A3S0S17G0A1Sf8R15S77RfA3S16G0ReA2A3S0S11SfaR16S77R10RfSeS5S76SeS5S76S15S5A1A3A3A5S12A3S0S11S147S65R11A2S12A3S0S11S169S65S25S6R18A1A1A2S12A3S0S11S55S25S6R19A1A1S53R15S6dR14S52A4A2S12A3S0S11S6bS25S6R1aA1A1R15A2S12A3S0S11S69R16A1S12A3S0S11SdeS23S6R1cA1A1A1S12A3S0S11S168S23S6R1dA1A1R19S6dS19S14A1M5SdfR16A6S12A3S0S11S152VXGL;S23S6R1eA1M6A1R1aS6dG5S27G6A1Se3S7R1eA1A8S12A3S0S5S144S77R1fR19R18S76A5R1eA3SfdS10S10S5S51A2M7S10S3cS1dA2M8A2S13G7G8S13S5S51R1fS53R1cS6dR1bS52A4A4S13S3cS1dZ3aS118A4A4S72A3S47S49Z3cS48Z2Z40A2A2R17A2VTR;S4dS3eVJAv;S53R1eS6dR1dS52A4A1R24R1aR19A5VFAM;R18R17A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;FR;Fs;Fbd;Ftv;Fk;Fd;FT;FE;FE1;FE0;").
Proof.
  intros E0 E1 E T d k tv bd s R rho tp b tp0 HE1 H4 Hwf4 H12 Hwf12 HFR Hd Hs HE He Hchk Htp Hnf Hnb Hbb Hwp HB HR HX HT HinT Hb.
  eapply TR_pre with (P := SPA segs (JAv (NDA tv fr_hvn bd ANone)) E rho tp).
  { intros w Hw. pose proof (SPA_axforms segs _ xf_mc rho E0 E1 tp w HE1 Hw) as Hw1. rewrite <- HE.
    assert (Hw2 : SPA segs (JAv (NDA tv fr_hvn bd ANone)) (E_mc2 E1 d) rho tp w).
    { unfold E_mc2. apply (SPA_reshape segs _ rho E1 4 _ _ tp w H4); [reflexivity | reflexivity | reflexivity | exact Hwf4 | | exact Hw1].
      intros HF. destruct (cm_rng rho _ d HF HFR Hd Hs) as (A1 & A2 & A3 & A4).
      unfold dst_obj, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia. rewrite A2, A3.
      change (bv_unsigned (eval rho (SAlu ALU_ADD d (cb4 vNC)))) with (uval rho (SAlu ALU_ADD d (cb4 vNC))). rewrite A1. unfold uval. lia. }
    unfold E_mc3. apply (SPA_reshape segs _ rho (E_mc2 E1 d) 12 _ _ tp w H12); [reflexivity | reflexivity | reflexivity | exact Hwf12 | | exact Hw2].
    intros HF. assert (HF' : Forall (holds rho) (ss_facts (ax_S E1))) by exact HF.
    destruct (cm_rng rho _ d HF' HFR Hd Hs) as (A1 & A2 & A3 & A4).
    unfold src_obj, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
    change (bv_unsigned (eval rho (SAlu ALU_ADD vF (SLit 32)))) with (uval rho (SAlu ALU_ADD vF (SLit 32))). rewrite A4. unfold uval. lia. }
  apply (purec_callT_xp segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           XP_memcpy Pre_mc [L_mc1; L_mc1] E s R rho tp (NDA tv fr_hvn bd ANone) bd (FAM b tp0)).
  - intros Ai rho1 tp1. cbn [map]. exact (CMEMCPY Ai rho1 tp1).
  - reflexivity.
  - reflexivity.
  - exact He.
  - exact Hchk.
  - exact Htp.
  - exact Hnf.
  - exact Hnb.
  - exact Hbb.
  - cbn [nd_bd]. apply payA_same. exact Hwp.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact (site_pure E s R rho tv bd HB HR HX).
  - intros Ai tr ms md Hsm HM HX'. exact (XP_memcpy_site segs AInv CST XGL ALA HCST HXGL Ai E memcpy_pc s R rho tp tr ms md Hsm HM HX' He).
  - intros L rho' tp' HL. cbn [In] in HL. assert (HL' : L = L_mc1) by (destruct HL as [<-|[<-|[]]]; reflexivity). subst L. cbn [nd_tv nd_fr nd_am]. rewrite HT.
    apply (REENTER T (NDA tv fr_hvn bd ANone) (58, z0)); [exact HinT | meas].
Qed.
Lemma XH_E_mk : ltac2:(tb__ "0|1|
S20SfS3fQ40A1A1M0S3cG0S47S49Z3cS48Z2Z40A2A2R2A2VTR;S4dS3eVJAv;S92A1S7eR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndk, ndF.
  apply (X_E_mc E_mk0 (E_mc1 E_mk0) E_mk T_mck vND vNK _ _ (s_mc E_mk vND vNK) R_mk rho tp b tp0 E_mk1_eq);
    [vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact E_mk_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact T_mck_eq | innth 14 | exact Hb].
Qed.
Lemma XH_E_mg : ltac2:(tb__ "0|1|
S20SfS3fQ40A1A1M0S3cG0S47S49Z3cS48Z2Z40A2A2R2A2VTR;S4dS3eVJAv;S91A1S7dR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndg, ndF, tvG.
  apply (X_E_mc E_mg0 (E_mc1 E_mg0) E_mg T_mcg vDg vKg _ _ (s_mc E_mg vDg vKg) R_mg rho tp b tp0 E_mg1_eq);
    [vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact E_mg_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact T_mcg_eq | innth 15 | exact Hb].
Qed.

Lemma XH_E_sm : ltac2:(tb__ "0|1|
S20SfS3fQ40A1A1M0S3cG0S47S49Z62S48Z2Z40A2A2R2A2VTR;S4dS3eVJAv;S8eA1S96R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF.
  apply (smalloc_callT segs AE_A AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           0 E_sm0 s_sm R_sm rho tp nd0 110 120 (FAM b tp0) CSM).
  - lia.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - intros A A' _; exact I.
  -
    intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK. destruct (P0_now rho Hav HP0) as (_ & _ & _ & _ & HC0).
    cbn [nd_tv nd_fr nd0 ND] in HN, HD, HZ, HFR |- *.
    split; [|split].
    + exact (siteP Ai rho _ (tv_hvn vND vNK) [] None R_sm rho1 tp1 md1 HM HF' ltac:(vmr) Hav HP0 HT HTK HBf HFF HN HD HZ HFR ltac:(vmr)).
    + exact (proj1 (proj2 (siteX Ai rho _ (tv_hvn vND vNK) [] None (ss_objs (ax_S E_sm0)) (ax_X E_sm0) rho1 tp1 md1 HM HF' ltac:(vmr) Hav HP0 HT HTK HBf HFF HN HD HZ HFR ltac:(vmr)))).
    + split; [change (wsub_get s_sm 12) with (SLit 64); rewrite uval_lit by lia; change (fs_frame_size 0) with 64; lia|].
      unfold ffpairs. change (map (fun y : Z * Z * Z => fst y) FF) with (map fst FF). rewrite HC0. cbn. lia.
  -
    intros rho' tp'. rewrite T_sm_eq.
    eapply TR_pre with (P := SPA segs (JAv ndp) T_sm1 rho' tp').
    { intros w Hw. exact (SPA_axforms segs _ [AXSelect sel_sm] rho' T_sm T_sm1 tp' w T_sm1_eq Hw). }
    apply (TR_pre (fun w => exists rho2, SPA segs (JAv ndp) C_pro rho2 tp' w)).
    { intros w Hw.
      destruct (JA_frame_open segs HTOP AInv CST XGL ALA HCST HXGL LFLAG NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue HKc HBX HNP
                  (tv_hvn vND vNK) fr_hvn (bd_hvn vNC vNK) ANone 0%nat 110 0 120
                  T_sm1 objs_sm1 (X_hvn vND vNK) [] rho' tp' w eq_refl ltac:(lia) eq_refl T_sm1_objs T_sm1_X
                  ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) eq_refl ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as (rho2 & _ & Hw2); [| exact Hw |].
      - intros Ai rho1 tp1 md1 HF2 HP0 Hav HM HT HTK HBf HFF HN HDt HZt HFR. rewrite app_nil_r.
        exact (proj1 (siteX Ai rho' _ (tv_hvn vND vNK) fr_hvn (Some 0%nat) (ss_objs (ax_S T_sm1)) (X_hvn vND vNK) rho1 tp1 md1 HM HF2 ltac:(vmr) Hav HP0 HT HTK HBf HFF HN HDt HZt HFR ltac:(vmr))).
      - exists rho2. rewrite app_nil_r in Hw2. rewrite C_pro0_eq in Hw2. rewrite <- C_pro_eq.
        apply (SPA_x_len0 segs (JAv ndp) C_pro0 110 5 rho2 tp' w); [vmr | lia | vmr | exact Hw2]. }
    apply TR_exw. intros rho2. apply (REENTER C_pro ndp (96, z0)); [innth 1 | meas].
Qed.

Lemma f32_rng : ltac2:(tb__ "0|1|
S20SfS1eA1S100S1eS28R2A1R1A3S0S11Se0R2A1S12A3S0S3cS66R4S26SdbS6eS1fZ20M0A1A3A2S4bS66R4S6eA2G0A2A3F_;F_;FF;Fr;").
Proof.
  intros r F HF HFR. pose proof (framez_of r F HF HFR) as [_ _ G3]. unfold IMG_HI in G3.
  pose proof (uval_range r vF). apply uval_add_litZ; lia.
Qed.

Lemma XH_X_rel : ltac2:(tb__ "0|1|
S20SfS3fQ40A1A1M0S3cG0S47S49Z5eS48Z2Z40A2A2R2A2VTR;S4dS3eVJAv;S73A1Sa5R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.

  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndp) C_ms rho' tp w)).
  { intros [tr [ms md]] Hw. exists (rho_absorb rho [shobj gF 0 8 cells_rel DZero] (vms md tp ms)).
    change C_ms with (shadow_release_stateA X_rel objs_rel 110 [(32, 12)]).
    apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue HKc HBX HNP
             (tv_hvn vND vNK) fr_hvn (bd_hvn vNC vNK) ANone 0%nat 110%positive 0 120%positive gF 0 8 cells_rel DZero X_rel objs_rel [(32, 12)] rho tp tr ms md
             eq_refl ltac:(lia) eq_refl X_rel_objs ltac:(lia) ltac:(vm_compute; split; discriminate) eq_refl ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)
             ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)); [|exact Hw].
    intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
    exact (siteF Ai rho _ (tv_hvn vND vNK) fr_hvn objs_rel rho1 tp1 md1 HM HF ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) Hav HP0 HT HTK HN HD HZ HFR ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)). }
  apply TR_exw. intros rho'.

  eapply TR_pre with (P := SPA segs (JAv ndp) E_ms rho' tp).
  { intros w Hw. pose proof (SPA_axforms segs _ _ rho' C_ms C_ms1 tp w C_ms1_eq Hw) as Hw1. unfold E_ms.
    apply (SPA_reshape segs _ rho' C_ms1 2 _ _ tp w C_ms1_o2); [reflexivity | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | | exact Hw1].
    intros HF. unfold xyz_obj, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
    change (bv_unsigned (eval rho' (SAlu ALU_ADD vF (SLit 32)))) with (uval rho' (SAlu ALU_ADD vF (SLit 32))).
    rewrite (f32_rng rho' _ HF ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)). unfold uval. lia. }

  apply (purec_callT_xp segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           XP_memset Pre_ms [L_ms] E_ms s_ms R_ms rho' tp ndp (bd_hvn vNC vNK) (FAM b tp0)).
  - intros Ai rho1 tp1. cbn [map]. exact (CMEMSET Ai rho1 tp1).
  - reflexivity.
  - reflexivity.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - cbn [nd_bd ndp ndF]. apply payA_same. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - unfold ndp, ndF. apply (site_pure E_ms s_ms R_ms rho' (tv_hvn vND vNK) (bd_hvn vNC vNK)); OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - intros Ai tr ms md Hsm HM HX'. exact (XP_memset_site segs AInv CST XGL ALA HCST HXGL Ai E_ms memset_pc s_ms R_ms rho' tp tr ms md Hsm HM HX' ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)).
  -
    intros L rho2 tp2 [<-|[]]. cbn [nd_tv nd_fr nd_am ndp ndF]. rewrite T_ms0_eq.
    eapply TR_pre; [|apply (REENTER C_body ndp (92, z0)); [innth 2 | meas]].
    intros w Hw. apply (SPA_axforms segs _ _ rho2 T_ms1 C_body tp2 w C_body_eq). unfold T_ms1.
    apply (SPA_reshape segs _ rho2 T_ms0 1 _ _ tp2 w T_ms0_o1); [reflexivity | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | | exact Hw].
    intros HF. unfold mid_xyz, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
    change (bv_unsigned (eval rho2 (SAlu ALU_ADD vF (SLit 32)))) with (uval rho2 (SAlu ALU_ADD vF (SLit 32))).
    rewrite (f32_rng rho2 _ HF ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)). unfold uval. lia.
Qed.

Lemma X_cm_Y : ltac2:(tb__ "0|5|
S5S5S1dS1dS51S20SfS3fQ40A1A1S12aS0S17S21A1M0SfeS21S27S6R8A1A1U1A3S16S21S2cS26SdbR6S109S107A1M1A3S1fZ0A1M2S1fZcA1M3S15S2aA1M4S2bA5A2A3S0G0SfeS21S27S6Se2R9R7A2A1A1U2A3S16S21S2cS26SdbS6eS1fZ20A1A3G2G3G4S2bA5A2A3S0S11S2fS25S6RaA1A1SeaR8A1A2S12A3S0S11S2fS25S6Se2RbR9A2A1A1SebA2S12A3S0S11Se0S23S6RcA1A1A1S12A3S0S11SfcS1eS29S22RbS24P1eA1A2A1S23S6RdA1A1A3S12A3S0S11SfcS1eS29S22G1S1fS119A1A2A1S23S6ReA1A1A3S12A3S0S17S5A1S42Se7Se2RfRdA2A1Se9A2S16S5ReA2A3S4dS3eVJAv;RcA1R10RbRaR9A6S4dS3eVJAv;RdA1R10RcRbRaA6F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fnd;Fk;Fd;FY;FX;").
Proof.
  intros X Y d k nd rho tp w H1 H2 Hwf1 Hwf2 HFR Hd Hs HY Hw.
  apply (SPA_axforms segs _ xf_cm rho (cm2 (cm1 X d)) Y tp w HY).
  assert (Hw1 : SPA segs (JAv nd) (cm1 X d) rho tp w).
  { unfold cm1. apply (SPA_reshape segs _ rho X 1 _ _ tp w H1); [reflexivity | reflexivity | reflexivity | exact Hwf1 | | exact Hw].
    intros HF. destruct (cm_rng rho _ d HF HFR Hd Hs) as (A1 & A2 & A3 & A4).
    unfold cm_dst, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia. rewrite A2, A3.
    change (bv_unsigned (eval rho (SAlu ALU_ADD d (cb4 vNC)))) with (uval rho (SAlu ALU_ADD d (cb4 vNC))). rewrite A1. unfold uval. lia. }
  unfold cm2. apply (SPA_reshape segs _ rho (cm1 X d) 2 _ _ tp w H2); [reflexivity | reflexivity | reflexivity | exact Hwf2 | | exact Hw1].
  intros HF. assert (HF' : Forall (holds rho) (ss_facts (ax_S X))) by exact HF.
  destruct (cm_rng rho _ d HF' HFR Hd Hs) as (A1 & A2 & A3 & A4).
  unfold cm_src, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
  change (bv_unsigned (eval rho (SAlu ALU_ADD vF (SLit 32)))) with (uval rho (SAlu ALU_ADD vF (SLit 32))). rewrite A4. unfold uval. lia.
Qed.

Lemma XH_X_epk : ltac2:(tb__ "0|1|
S20SfS3fQ40A1A1M0S3cG0S47S49Z37S48Z2Z40A2A2R2A2VTR;S4dS3eVJAv;S92A1Sa3R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  eapply TR_pre.
  { intros w Hw. apply (X_cm_Y X_epk Y_epk vND vNK ndk rho tp w); [vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact Y_epk_eq | exact Hw]. }
  apply (X_Y_ep Y_epk C_epk _ _ vND vNK rho tp b tp0); [vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_epk_eq | innth 16 | exact Hb].
Qed.
Lemma XH_X_epg : ltac2:(tb__ "0|1|
S20SfS3fQ40A1A1M0S3cG0S47S49Z37S48Z2Z40A2A2R2A2VTR;S4dS3eVJAv;S91A1Sa2R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  eapply TR_pre.
  { intros w Hw. apply (X_cm_Y X_epg Y_epg vDg vKg ndg rho tp w); [vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact Y_epg_eq | exact Hw]. }
  apply (X_Y_ep Y_epg C_epg _ _ vDg vKg rho tp b tp0); [vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_epg_eq | innth 17 | exact Hb].
Qed.

Lemma X_X_rl : ltac2:(tb__ "0|6|
S5S5S5SfS10S1dS1dA2A1SfS67A1S20SfS3fQ40A1A1M0S3cG0S0S17S5A1S42R9SeS41S43S7cA1S15S41A1A3A2S16S5R8A2A3S0S5S8R9S16eS6R9A1M1S102S21UcM2S27G1A1A3A2A2R8A3S0S11S156P6eP78S70Z0S103S21G2S27S6RaA1A1A3A5S12A3S0S11ScSeS1eS31SaS70A1S6eA2SeS1eS22S24S70A1S1fS4cS48Z2M3Z3dA2Z1A2A1A2S15S1eA1A3A3S23S6RbA1A1A2S12A3S0S11S55S25S6RcA1A1S53RaS6dR9S52A4A2S12A3SfdS10S10S5S51A2M4S10S3cS1dA2M5A2S13G4G5S13S5S51RcS53RbS15S10S10S1dS3cA2S1dA2A1RaS52A4A4S13S3cS1dZ28S118A4A4S72A3S47S49Z2dS48G3Z40A2A2R8A2VTR;S4dS3eVJAv;S53RdS6dRcS52A4A1R10RbRaA5VFAM;R9R8A2A2F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fbd;Ftv;FC;FX1;FX;").
Proof.
  intros X X1 C tv bd rho tp b tp0 HX1 HC HR Hfe Hnb HinC Hb.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv (NDA tv [] bd ANone)) C rho' tp w)).
  { intros [tr [ms md]] Hw. pose proof (SPA_axforms segs _ [AXSelect sel_rel] rho X X1 tp _ HX1 Hw) as Hw1.
    exists (rho_absorb rho (skipn 12 (ss_objs (ax_S X1))) (vms md tp ms)). rewrite <- HC.
    change (ax_setS X1 (set_objs (ax_S X1) (firstn 12 (ss_objs (ax_S X1))))) with (drop_lastA X1 (firstn 12 (ss_objs (ax_S X1)))).
    change (@nil (sv * Z * sv)) with (remove_nth 0 fr_hvn).
    apply (JA_release_inline segs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok AInv CST XGL ALA HCST HXGL LFLAG LFSH NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue HKc HBX HNP
             tv fr_hvn bd ANone 0%nat 110%positive 0 120%positive gF X1 (firstn 12 (ss_objs (ax_S X1))) (skipn 12 (ss_objs (ax_S X1))) rho tp tr ms md);
      [reflexivity | lia | symmetry; apply firstn_skipn | exact HR | exact Hfe | exact Hnb | intros A1 A2 _; exact I | exact Hw1]. }
  apply TR_exw. intros rho'. apply (REENTER C (NDA tv [] bd ANone) (40, z0)); [exact HinC | meas].
Qed.
Lemma XH_X_rlk : ltac2:(tb__ "0|1|
S20SfS3fQ40A1A1M0S3cG0S47S49Z2dS48Z2Z40A2A2R2A2VTR;S4dS3eVJAv;S92A1Sa9R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_X_rl X_rlk _ C_rlk _ _ rho tp b tp0 X_rlk_eq); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | innth 20 | exact Hb].
Qed.
Lemma XH_X_rlg : ltac2:(tb__ "0|1|
S20SfS3fQ40A1A1M0S3cG0S47S49Z2dS48Z2Z40A2A2R2A2VTR;S4dS3eVJAv;S91A1Sa8R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_X_rl X_rlg _ C_rlg _ _ rho tp b tp0 X_rlg_eq); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | innth 21 | exact Hb].
Qed.
Lemma XH_X_rlf0 : ltac2:(tb__ "0|1|
S20SfS3fQ40A1A1M0S3cG0S47S49Z2dS48Z2Z40A2A2R2A2VTR;S4dS3eVJAv;S81A1Sa6R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_X_rl X_rlf0 _ C_rlf0 _ _ rho tp b tp0 X_rlf0_eq); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | innth 22 | exact Hb].
Qed.
Lemma XH_X_rlf1 : ltac2:(tb__ "0|1|
S20SfS3fQ40A1A1M0S3cG0S47S49Z2dS48Z2Z40A2A2R2A2VTR;S4dS3eVJAv;S81A1Sa7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_X_rl X_rlf1 _ C_rlf1 _ _ rho tp b tp0 X_rlf1_eq); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | innth 23 | exact Hb].
Qed.

Lemma X_P_ok : ltac2:(tb__ "0|1|
S20SfS3fQ40A1A1M0S3cG0VTR;S4dS3eVJAv;S90A1S89R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. innth 0. Qed.
Lemma X_P_fail : ltac2:(tb__ "0|1|
S20SfS3fQ40A1A1M0S3cG0VTR;S4dS3eVJAv;S8fA1S88R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. innth 1. Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S5S51S10S3cS1dA2M0S20SfS3fQ40A1A1M1G1SfdS10S10S5S51A2M2G0A2S13G2G0S13S5S51R6R5A4R4A4S8dA3VTR;S4dS3eVJAv;R6A1R7R4R3A5VFAM;S5eS13G2G0S13S5S51R7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsH] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]]]]]]]; injection H as <- <- <-.
  - apply XH_E_sm. meas. - apply XH_X_rel. meas. - apply XH_E_A. meas. - apply XH_E_B. meas. - apply XH_E_C. meas.
  - apply XH_E_vr. meas. - apply XH_E_mk. meas. - apply XH_E_mg. meas.
  - apply XH_X_epk. meas. - apply XH_X_epg. meas. - apply XH_X_epf0. meas. - apply XH_X_epf1. meas.
  - apply XH_X_rlk. meas. - apply XH_X_rlg. meas. - apply XH_X_rlf0. meas. - apply XH_X_rlf1. meas.
  - apply X_P_ok. - apply X_P_fail.
Qed.
End X.

Definition keep_ejcertH_ok : list sprop := ltac2:(tb__ "0|5|
SeS1eS22S24PcA1S1fZ800000000000A1M0A2SeS1eS22S24PdA1G0A2SeS1eS22S26SdbS24P36A1M1S39SdcS1fZ4A1S24P38A1M2A3M3A3S24P1eA1A2SeS1eS22G1G0A2SeS1eS22S24P37A1G2A2SeS1eS22G2S1fZffffffffA1M4A2SeS1eS22G3G4A2S15S1eA1A3A3A3A3A3A3A3").
Definition H_ejcertH_ok : list sprop := ltac2:(tb__ "0|0|
S170S14fS1bS57S72S8dA3A2").
Lemma ejcertH_ok : ltac2:(tb__ "0|1|
S0S11S61S3eS65SbfSd2P64S101S57S57S16fS14eA1M0S72A4S101S57S57G0S8dA4A7S12A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S64S3eVKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S160S3eS158VAInv;VCST;VXGL;A5").

Theorem handle_vn_sum : ltac2:(tb__ "0|0|
SfS3fQ40A1A1S12cS3eVok;S4dS3eS5aVAInv;VCST;VXGL;VKc;SddVCST;VFB;VFF;A3VFB;VFF;VBX;S54S8eAaS99Vrho0;R1A5Sf6S3eS65Vrho0;R1S14cA5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA_h segs AInv CST XGL NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue HKc ALA H_ejcertH_ok FUEL_hvn cutpcs_hvn 100 cutsH exitsH ok (Q tp0) Hok ejcertH_ok)
         with (ndT := nd0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0 & Hin). cbn in E0. injection E0 as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsH)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (call_soundPA3 segs ok)) with (rvX := rv) (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (vec_reserve_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ok Hok AC tp1).
       - intros Ai rho1 tp1. apply (aca_stack_malloc _ _ _ _ _ AC 0 ltac:(cbn; tauto)); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
       - intros Ai rho1 tp1. apply (aca_asan_memset _ _ _ _ _ AC); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
       - intros Ai rho1 tp1. apply (aca_asan_memcpy _ _ _ _ _ AC); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA segs AInv CST XGL NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue HKc ALA ok Cl Pre_sd s R Posts_sd rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply scan_double_sum; [apply frozen_ok_frameA; exact Hok | apply (frozen_stableA' NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue ok (map edropA cutsH) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NF Kc (P0_hvn CST FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_hvn P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S161S3eS158VAInv;VCST;VXGL;A5").

Theorem handle_vn_sum_ex : ltac2:(tb__ "0|0|
SfS3fQ40A1A1S12bS3eS4dS3eS5aVAInv;VCST;VXGL;VKc;SddVCST;VFB;VFF;A3VFB;VFF;VBX;S54S8eAaS99Vrho0;R1A5Sf6S3eS65Vrho0;R1S14cA5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA_h segs AInv CST XGL NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue HKc ALA H_ejcertH_ok FUEL_hvn cutpcs_hvn 100 cutsH exitsH (Q tp0) ejcertH_ok)
         with (ndT := nd0) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue) cutsH) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (@etriple_ex segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (vec_reserve_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ACX tp1).
       - intros Ai rho1 tp1. apply (acx_stack_malloc _ _ _ _ _ ACX 0 ltac:(cbn; tauto)). exact HKc.
       - intros Ai rho1 tp1. apply (acx_asan_memset _ _ _ _ _ ACX). exact HKc.
       - intros Ai rho1 tp1. apply (acx_asan_memcpy _ _ _ _ _ ACX). exact HKc.
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA_ex segs AInv CST XGL NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue HKc ALA Cl Pre_sd s R Posts_sd rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply scan_double_sum_ex. apply (frozen_stableA' NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue cutsH T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NF Kc (P0_hvn CST FB FF) FB FF BX PTrue rho0 tp0 nd Posts_hvn P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_handle_vn_pf.

(* [comment removed for export] *)
Module Asan_memcpyR.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "app"; "bool"; "list"; "pair"; "true"; "nat"; "prod"; "None"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "SVar"; "valuation"; "DUnknown"; "FcsrFrm0"; "cell"; "mkObj"; "mkSS"; "ss_objs"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "A_globals"; "mkA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Asan_memcpyR"; "CR"; "PR"; "objsLR"; "FUELR"; "PostsR"; "PreWR"; "vcutsR"; "vexitsR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "cut_regs"; "pre_fregs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "leafA"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_memcpy_contract"; "R_rtc"; "carve_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "NPOSTM"; "ae_ret_asan_memcpy"; "memx_depth"; "pre_facts"; "stack_win"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpyR_iface"; "L_memcpyR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGlueA"; "check_ecfgIA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgEdgesA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Asan_memcpy_contract.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_memcpy_contract OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpyR_iface.
Import ListNotations.
Close Scope bv_scope. Open Scope Z_scope.

Definition PreWR (src : Z) : axst := Pre_memcpyR AE_A src 12.
Definition CR (src : Z) : axst := ltac2:(tb__ "0|1|
S2dS21Vsrc;A1M0S31S2bG0A1A1A2").

Definition objsLR : list sobj := ltac2:(tb__ "0|0|
S2ScS0ScS39S0ScS13SePcA1SdZ0A1SdZcA1S1S12A1S10A5S1ScA1A3A3S18A3").
Definition PR (src : Z) : axst := ltac2:(tb__ "0|2|
S19S14S36S34A1S27S25S24A1S0S8S7SbA2M0S5S7SbUaSePcA1A4S1G0A1A3A2S26S11S9SbA1S2ScS1eS30A3S38S37A1S35SaA9S0S8SbSbA2M1S5SbSbSeP35A1SeP36A1A4S0G1S5SbSbSdVsrc;A1SdZcA1A4S1G1A1A3A3A2").
Definition PostsR (src : Z) : list leafA := ltac2:(tb__ "0|0|
S0S2eS2fS1dVsrc;A1S3eA2S1S2eA1A3").

Lemma PR_objs : ltac2:(tb__ "0|0|
S1bS1aS4ScA1S15S2bS1dR1A1A1A1S2ScS1eS30A3A3Fsrc;"). Proof. reflexivity. Qed.

Lemma PR_unobj : ltac2:(tb__ "0|1|
S1bS1aS2cS2dS1dR1A1M0S3fS2bG0A1S1eA2A2S3bS34R1ZcA3A3Fsrc;"). Proof. reflexivity. Qed.
Lemma swf_CR : ltac2:(tb__ "0|0|
S1bS1aS3S16S2bS1cR1A1A1A1S6A3Fsrc;"). Proof. intros src. reflexivity. Qed.

Definition FUELR : nat := 1500%nat.
Definition vcutsR (src : Z) : list vnodeA := ltac2:(tb__ "0|0|
S0S28S29S1cVsrc;A1Z1SdZ0A1A3S1S28A1A3").
Definition vexitsR (src : Z) : list vnodeA := ltac2:(tb__ "0|0|
S0S28S29S1dVsrc;A1Z0SdZ1A1A3S1S28A1A3").
Definition certR (src : Z) : Prop := ltac2:(tb__ "0|0|
S1aS3S40S17S1fS1S1bA1S24S22Vsrc;A1S23Vsrc;A1A6S6A3").

Lemma echeckR_hv : certR white_hv. Proof. unfold certR. vm_cast_no_check (eq_refl true). Qed.
Lemma echeckR_lo : certR white_lo. Proof. unfold certR. vm_cast_no_check (eq_refl true). Qed.

Section Core.
Variable src : Z.
Hypothesis Hcert : certR src.

Lemma checkR : ltac2:(tb__ "0|1|
S1aS3S2aS17S1fS1S1bA1S24S0S2cS1cVsrc;A1S1S2cA1M0A3S0S2cS1dVsrc;A1G0A3A6S6A3").
Proof. exact (check_cfgA_of_ecfgIA segs FUELR [] NF (vcutsR src) (vexitsR src) [CR src] [PR src] eq_refl eq_refl Hcert). Qed.

Section Sum.
Variable ok : world -> Prop.
Variable J : jpredA.
Hypothesis Hok : ok_frameA segs ok J.
Hypothesis Hst : stableA segs NF J.

Theorem coreR_sum : ltac2:(tb__ "0|0|
SfS4S3aQ40A1A1S3dS17Vok;S33S17VJ;S1cVsrc;A1R2R1A5S32S17VJ;S24R2R1S20Vsrc;A1A6A4Ftp;Frho;").
Proof.
  intros rho tp.
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  assert (HokG : ok_frameA segs ok (withGA (fun r => agree_below NF rho r) J)).
  { intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto. }
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF (CR src) rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUELR [] NF [CR src] [PR src] (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp (PostsR src)) tp HokG HstG checkR); [|left; reflexivity].
  intros E rhoE HinE. destruct HinE as [<-|[]]. apply exit_postA. left; reflexivity.
Qed.
End Sum.

Section SumEx.
Variable J : jpredA.
Hypothesis Hst : stableA segs NF J.

Theorem coreR_sum_ex : ltac2:(tb__ "0|0|
SfS4S3aQ40A1A1S3cS17S33S17VJ;S1cVsrc;A1R2R1A5S32S17VJ;S24R2R1S20Vsrc;A1A6A3Ftp;Frho;").
Proof.
  intros rho tp.
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF (CR src) rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_complete_autoIA segs FUELR [] NF (vcutsR src) (vexitsR src) (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp (PostsR src)) tp HstG) with (n := mkVNA (CR src) 1 (SLit 0)); [ | exact Hcert | | left; reflexivity].
  { intros m [<-|[]]. apply Pos.le_refl. }
  intros E rhoE HinE. destruct HinE as [<-|[]].
  apply (eexit_post_IA0 segs J NF rho (vcutsR src) (PostsR src) (mkVNA (PR src) 0 (SLit 1))). left; reflexivity.
Qed.
End SumEx.
End Core.
End Asan_memcpyR.

(* [comment removed for export] *)
Module Fps_pre.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "list"; "nil"; "pair"; "prod"; "option"; "bool"; "true"; "None"; "app"; "Some"; "andb"; "false"; "length"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "SPUle"; "sobj"; "SVar"; "SAlu"; "sstate"; "ss_next"; "SPAlign"; "cell"; "ob_base"; "ss_objs"; "ss_regs"; "SPEq"; "mkObj"; "mkSS"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "odefault"; "ss_lenient"; "ss_pc"; "DUnknown"; "FcsrFrm0"; "c_off"; "sprop_below"; "sprop_eqb"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_resv"; "sv_eqb"; "tfact"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre"; "BASEF"; "D_FPS"; "facts_fps"; "FQC"; "CUTS_FPS"; "FQB"; "FUEL_T"; "O_fwin"; "TPL"; "X_fps"; "drop_cellsF"; "facts_in"; "keep_cell"; "mc_entry"; "mc_musl"; "mc_ret"; "objs_fps"; "prune0"; "regs_fps"; "setF"; "set_facts"; "sp_off"; "str_facts"; "vfp_entry"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "ALU_ADD"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st"; "sX"; "vXL"; "vXB"; "vXO"; "O_cfsl"; "O_realmc"; "O_realsn"; "O_strS"; "factsB"; "factsS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "ax_setS"; "la_reason"; "la_state"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "AXMerge"; "AXRebase"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"; "opp"; "leb"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "filter"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf"; "ms16"; "O_cflag"; "O_realm"; "O_realv"; "O_rtc2"; "O_ssp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "two62"; "NF"; "pre_fregs"; "pre_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "A_globals"; "mkA"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFpIface"; "fp_entry"; "fp_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface"; "FERR"; "O_ferr0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy"; "O_rtc3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region"; "HSE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region.RegionAddr"; "rip_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Icpt_strnlen_st"; "si_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_istrlen.ISLAddr"; "isl_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB"; "replace_obj_at"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymObj SymBytes SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ListObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform ListCommitA DrvGlueB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Musl_wl_err.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvFpIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fn.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_memchrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fk.Str_strnlenA_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Icpt_strnlen_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_istrlen OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Musl_wl_err OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.DrvFwStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFpIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.DrvFpStates.
Import ListNotations. Import MCHAddr. Import RegionAddr. Import ISLAddr.
Close Scope bv_scope. Open Scope Z_scope.

Definition FMT_COPEN : Z := 0x1eec6.
Definition FMT_RDERR : Z := 0x1eedb.
Definition FMT_USAGE : Z := 0x1608d.
Definition TPL : Z := 0x6245b8.
Definition D_FPS : Z := 1024 + D_SI.
Definition O_fwin : sobj := ltac2:(tb__ "0|0|
S1fS15PaA1S12S6aS37A1A1S12Z0A1S3S1aA1S28A5").
Definition str_facts : list sprop := ltac2:(tb__ "0|9|
S0S11S13S16S4fS15P10A1M0S12Z8A1M1A3S15P11A1M2A2S0S11S13G1G2A2S0S11S13G2S12S77A1M3A2S0S11S13S12Z1A1M4S51A2S0S11S13S51G3A2S0S11S13S16S4fS54G2A3S52A2S0S11S13S54S52A2S0S11S13G2S52A2S0S11S13S52S12S68Z2M5Z28A2A1A2S0S11S13S12S84A1S53A2S0S11S13S16S4fS53S52A3M6S12S68G5Z2fA2M7A1A2S0S11S13S53S12S69G7Z40A2A1A2S0S11S19P12Z6M8A2S0S11S19P13G8A2S0S11S13S16S4fS51G4A3G6A2S0S11S13G0S12Z1ffffA1A2S0S11S13S15PaA1S51A2S0S11S13S16S4fG0S12Z10A1A3G2A2S3S11A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition facts_fps : list sprop := ltac2:(tb__ "0|2|
SaS11S0S11S19PaM0Z4A2S0S11S13S12Z7fff7ffff000A1S15G0A1M1A2S0S11S13G1S12S69S68Z2Z2fA2Z10A2A1A2S0S11S71Z918A1S3S11A1A3A3A3A3S4cA3").
Definition X_fps (fblk flen : Z) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S5S10S10A2M0S4S10S10S12Vfblk;A1S12Vflen;A1A4S0G0S4S10S10S53S52A4S0G0S4S10S10S16S4fS15PaA1S12S6aS37A1A1A3S12S37A1A4S3G0A1A3A3A3").
Definition objs_fps : list sobj := ltac2:(tb__ "0|0|
SaS14S0S14S3dS0S14S58S0S14S82S0S14S83S0S14S75S0S14S72S0S14S74S0S14S73S0S14S56S0S14S57S0S14S55S0S14S76S3S14A1A3A3A3A3A3A3A3A3A3A3A3A3S7cA3").
Definition regs_fps (fmt : Z) : list sv := ltac2:(tb__ "0|1|
S7bS7aS0S5S1S10A2M0S4S1S10U3S12Z10800A1A4S0G0S4S1S10U4S12S3eA1A4S0G0S4S1S10UaS12S81A1A4S0G0S4S1S10UbS12Vfmt;A1A4S0G0S4S1S10UcS51A4S3G0A1A3A3A3A3A3A2").
Definition Pre_fps (fmt fblk flen : Z) : axst := ltac2:(tb__ "0|0|
S7dS20S7fS48Vfmt;A1S79S29S9S10A1S46S38S78SdA9S3fVfblk;Vflen;A2A2").
Definition Pre_co : axst := Pre_fps FMT_COPEN 0x1eec0 0x80.

Definition mc_entry : Z := 0x5d6d8.
Definition mc_musl : Z := 0xddf74.
Definition mc_ret : Z := 0x5d808.
Definition vfp_entry : Z := 0xda7b0.
Definition CUTS_FPS : list Z := ltac2:(tb__ "0|0|
S0S33S87S0S33S86S0S33S85S0S33S4dS0S33S43S0S33S44S0S33S45S0S33Zd9ad4S0S33S80S3S33A1A3A3A3A3A3A3A3A3A3").

Definition setF (S : sstate) (F : list sprop) : sstate := ltac2:(tb__ "0|0|
S20S27VS;A1S1dVS;A1S2fVS;A1S2eVS;A1S30VS;A1S1cVS;A1VF;S18VS;A1S26VS;A1A9").
Definition set_facts (A : axst) (F : list sprop) : axst := ltac2:(tb__ "0|0|
S5eVA;S49S5bVA;A1VF;A2A2").
Definition keep_cell (lo : Z) (c : cell) : bool := ltac2:(tb__ "0|3|
S10S7Lx;S2aVc;A1S33S6bVlo;R1A2Lo;S34S8Li;S4eS10S10S8Lb;La;M0Lop;M1G1S50G0Lop;M2G2S7S35S10S8La;Lw;Lsgn;S34S10S33S8Lk;Li;Ll;X10x8").
Definition drop_cellsF (keep : cell -> bool) (o : sobj) : sobj := ltac2:(tb__ "0|0|
S1fS1bVo;A1S24Vo;A1S23Vo;A1S6eS1aVkeep;S21Vo;A1A3S22Vo;A1A5").

Definition sp_off (S : sstate) (b : sv) : option Z := ltac2:(tb__ "0|a|
S10S6S33A1M0Lx;S70S10U2S1dVS;A1S12Z0A1A4S33S9S33A1M1Lz;S34G1Li;M2S4eS10S10S4eG0Lop;R3S10G0Lb0;R1S33S7G0L_;S31R3Vb;A2SbS33R1A2G1X7x2Lo;G2S4eS10S10G1Lb1;La;M3Lop0;M4G4S50G3Lop0;M5G5S7S35S10G1La;Lw;Lsgn;M6S34S10S33G1Lk;Li;Ll;M7X10x8G1G1G1G1G1G1G1G1G1X4exaLb0;Le;Lop;S4eS10S10G1Lb0;La;M8Lop;S50G8Lop;M9G9G6G7X10x8").
Definition prune0 (S : sstate) : option sstate := ltac2:(tb__ "0|4|
S2S14A1M0S6S17A1M1Lx;S1cVS;A1S9S17A1M2S14G0S25G1Lx;S22R2A1S6S33A1G1Lx;S4bVS;S1bR2A1A2S33S89VS;U0S40S42R1A1R3A2A3S17S7G1L_;S88VS;R1A2SbS17R1A2G2X7x2TT;Llo;G2X6x2G2G2S34G2Ll;M3G3S33S10S2S5S33S33A2A1S2S32A1G2Ltmpl;Lflds;Lcnt;Lesz;X25x6Ll;Lo;X2x2").
Definition trim (F : list sprop) (A : axst) : axst := ltac2:(tb__ "0|0|
S4aVA;VF;A2S5dS6S17A1S5dLx;S47S5bR1A1A1S17S5eR2R1A2LT;R1X6x2TA1;").

Definition facts_in (F : list sprop) (S : sstate) : bool := ltac2:(tb__ "0|0|
S6cS11S11S6dS11S2cR1A1S2dVS;A1A3Lf;VF;A3").
Definition FUEL_T : nat := 4000%nat.

Definition seg0 (A : axst) : option axst := ltac2:(tb__ "0|5|
S6S2S5cA1M0A1S6S5dA1M1Lx;S61S7eS3cS3aVA;S8A5G0G0G1Ll;R1S9S5dA1M2S5cG0G0G1Ll0;R1S67G1Lx;S5fR2A1G2S7G1L_;ScS8aS18S5bVA;A1A1S18S5bS60R2A1M3A1M4A1A2SfS26G4A1A1A2SbS5dG3A2G2X7x2G2G2G2G2G2X67x7S5cG0G2Ll2;Ll1;X2x2Ll0;LL;X2x2Ll;G2X6x2").

Fixpoint runp (Fs : list (list sprop)) (A : axst) : option axst :=
  match Fs with
  | [] => Some A
  | F :: Fs' => match seg0 (trim F A) with Some B => runp Fs' B | None => None end
  end.

Definition fs_ok (Fs : list (list sprop)) (S : sstate) : bool := ltac2:(tb__ "0|1|
S6cS2S11A1M0G0ScS41R1VS;A2S6cS11S2bS18VS;A1A1R1A3A2LF;VFs;A3").

Definition BASEF : list sprop := ltac2:(tb__ "0|2|
S0S11S19PaM0Z4A2S0S11S13S12Z7fff7ffff000A1S15G0A1M1A2S0S11S13G1S12S69S68Z2Z2fA2Z10A2A1A2S0S11S71Z918A1S3S11A1A3A3A3A3").

Definition FQC : list sprop := ltac2:(tb__ "0|0|
S0S11S1eS15P8cA1S15P10A1A2SaS11S5aS38A3A3").
Definition FQB : list sprop := ltac2:(tb__ "0|0|
S0S11S1eS15P8cA1S15P10A1A2SaS11S59S38A3A3").
Definition STRP : list sprop := ltac2:(tb__ "0|0|
S0S11S13S12Z1A1S51A2S0S11S13S51S12S77A1A2S3S11A1A3A3").

Definition FSS : list (list sprop) := ltac2:(tb__ "0|1|
S0S2S11A1M0S39S0G0S36S0G0S36S0G0S36S0G0S36S0G0S36S0G0S36S0G0S39S3G0A1A3A3A3A3A3A3A3A3").
Definition FSB : list (list sprop) := ltac2:(tb__ "0|1|
S0S2S11A1M0S36S0G0S36S0G0S36S0G0S36S0G0S36S0G0S36S0G0S36S0G0S3bS3G0A1A3A3A3A3A3A3A3A3").
Definition sho (A : axst) : ltac2:(tb__ "0|0|
S2S5S5S5S10S10A2S10A2S1A2A1") := ltac2:(tb__ "0|2|
S6fS14S5S5S5S10S10A2M0S10A2M1S1A2S14S4G1S1S4G0S10S4S10S10S1bR1A1S24R1A1A4S23R1A1A4SeS1aS21R1A1A2A4Lo;S1cS5bVA;A1A1A4").
Definition shl (r : option (list leafA)) : ltac2:(tb__ "0|0|
S2S5S5S33S67A2S34A2A1") := ltac2:(tb__ "0|4|
S6S2S5cA1M0A1S2S5S5S33S67A2M1S34A2M2A1Lr;Vr;G0S6fS5cG2S5cS4G1S34S4S33S67S27S5bS60R1A1A1M3A1S5fR1A1A4S18G3A1A4Ll;R1A4Lls;S3G2A1X6x2").

Definition XF6 : list axform := ltac2:(tb__ "0|11|
S0S62S65U0M0A1S0S62S63S0S1U5M1S0S1G0S0S1U6M2S0S1U4M3S0S1U7M4S0S1U8M5S0S1U1M6S0S1U9M7S0S1UaM8S0S1UbM9S0S1UcMaS0S1UdMbS0S1UeMcS0S1UfS0S1U2MdS0S1U3MeS3S1A1MfA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S62S64G0A1M10S0S62G10S0S62S66G0S12N400A1A2S0S62S63S0S1GdS0S1G0S0S1G6S0S1GeS0S1G3S0S1G1S0S1G2S0S1G4S0S1G5S0S1G7S0S1G8S0S1G9S0S1GaS0S1GbS0S1GcGfA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S3S62A1A3A3A3A3A3A3").

Definition zvar (T : axst) : positive := ltac2:(tb__ "0|4|
S10S34Lx;S70S10UaS1dS5bVT;A1A1S12Z0A1A4S33P1M0Lz;S34R1Lv;S4eS10S10G0Lb;La;M1Lop;M2G2S50G1Lop;M3G3S7S35S10G0La;Lw;Lsgn;S34S10S33G0Lk;Li;Ll;X10x8").
End Fps_pre.

