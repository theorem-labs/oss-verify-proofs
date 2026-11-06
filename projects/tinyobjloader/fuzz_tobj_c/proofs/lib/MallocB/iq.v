(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io i9.
From Stdlib Require NArith PArith.
From LinuxProcessSemantics.Riscv Require Decode DecodeC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.

(* [comment removed for export] *)
Module SegQ3D_qc_defs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "nat"; "pair"; "bool"; "list"; "true"; "option"; "prod"; "app"; "Some"; "false"; "None"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "ss_next"; "valuation"; "SVar"; "ss_facts"; "sprop_below"; "SLit"; "ss_objs"; "FcsrFrm0"; "SPAlign"; "agree_below"; "mkSS"; "ss_lenient"; "ss_regs"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "la_state"; "ax_X"; "ax_setS"; "axwf"; "mkLeafA"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qc_defs"; "Cqc"; "RCr"; "sC"; "PostsQC"; "RC0"; "TC1"; "TQCf"; "TQC"; "KEPTC"; "TC2"; "idxC"; "renC"; "runCr"; "FRAMEC"; "RESTC"; "TC4"; "factsC"; "objsC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states"; "PreQC"; "PostQC"; "QCRET"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "LQA"; "stableA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM"; "vmap"; "chkNM"; "entsM"; "keepsM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr"; "TR"; "JOK"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "pre_facts"; "O_got"; "O_rtc"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM"; "MC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states"; "QCRET2"; "RC"; "DQC"; "DQCs"; "clsB"; "mkD"; "vB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states"; "vXF"; "vXK"; "vXL"; "vXS"; "FRlo"; "O_cbD"; "O_mtx00"; "SWD"; "cb_cells"; "NXR"; "WLOW"; "spD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states"; "DEPTH_R"; "O_gmax"; "cbC"; "@Stdlib.Lists.List"; "forallb"; "In"; "fold_right"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "NPRE"; "O_sb"; "runA"; "add"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "obj_subst"; "sprop_subst_opt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states"; "optR"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition renC : wsub := ltac2:(tb__ "0|2|
S0S8S3eSeA2M0S3S3eSePaS66A4S0G0S3S3eSePfM1S75S12G1A1S15Zc0A1A2A4S0G0S3S3eSePcS69A4S0G0S3S3eSePeS58A4S0G0S3S3eSeP7fS12PceA1A4S0G0S3S3eSeP80S12PcfA1A4S0G0S3S3eSeP81S12Pc9A1A4S0G0S3S3eSeP83S12Pd1A1A4S1G0A1A3A3A3A3A3A3A3A3").
Definition objsC : list sobj := ltac2:(tb__ "0|0|
S6dSdSdS7cS33A1S16S1eS3bA1A1A4").
Definition factsC : list sprop := ltac2:(tb__ "0|1|
S6cS5SfA1M0SfSfG0S7SfA1G0Lx;S7dS33R2A2SfS0SfR1R2A3Lg;R1X7x2Lacc;Lf;S1SfA1S13S1eS3bA1A1A5").
Definition FRAMEC : list sobj := ltac2:(tb__ "0|0|
S0SdS5fS0SdS60S63A1S0SdS62S5cS5bS5dS5eA4S0SdS61S0SdS68S1SdA1A3A3A3A3A3").
Definition Cqc : axst := ltac2:(tb__ "0|1|
S52S1aS56S1cS1eS57A1M0A1S7aS17ScSeA1S9SdS39S35A3S9SfS13G0A1S9SfS38S0SfS18P97ZcA2S1SfA1A3A3A3S64SbA9S1S8SeSeA2A1A2").
Definition sC : wsub := ltac2:(tb__ "0|0|
S7bP1S1eS28A1S1eS3bA1A3").
Definition RC0 : list sobj := ltac2:(tb__ "0|0|
S80S6fS28S3bS2aA3A1").
Definition PostsQC : list leafA := ltac2:(tb__ "0|0|
S0S20S25S3cS7eA2S1S20A1A3").
Definition TQC : axst := ltac2:(tb__ "0|0|
S70S2aS3bS3cS28S2cA5").
Definition TQCf : axst := ltac2:(tb__ "0|0|
S6eS2fS13S1eS28A1A1A2").

Lemma Cqc_wf : ltac2:(tb__ "0|1|
S27S26S4S24S28A1S6A3S27S26S4S1dS1eS28A1A1S6A3S26S5S8SeSeA2M0A1S22S28A1S1G0A1A3A2A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RC0_eq : RC0 = FRAMEC. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HeC : ltac2:(tb__ "0|1|
S26S7S5SdA1M0A1S6fS28S3bS2aA3SaG0S2cA2A3"). Proof. vm_cast_no_check (eq_refl (Some FRAMEC)). Qed.
Lemma HchkC : ltac2:(tb__ "0|0|
S26S4S71S28S3bS2aS2cS6dS20S1fS21S2bA4A5S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HTC : ltac2:(tb__ "0|0|
S20S6bS20R1S2bA3S26S1fS70S2aS3bS21R2A1S28S2cA5S2fA3F_;FP;"). Proof. intros P [<-|[]]. reflexivity. Qed.
Lemma FBCC : ltac2:(tb__ "0|1|
S26S4S6aSfS14S10S1eS28A1M0A1A1S13G0A1A3S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBTC : ltac2:(tb__ "0|0|
S26S4S6aSfS14S10S1eS2fA1A1A1S13S1eS28A1A1A3S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXCC : ltac2:(tb__ "0|0|
S76S72S10S1eS28A1A1A2"). Proof. unfold Pos.le. cbn. discriminate. Qed.

Definition idxC : list nat := ltac2:(tb__ "0|0|
S0S2U0S0S2U7S0S2U8S0S2U9S0S2UaS0S2UbS0S2U5S0S2U6S0S2U4S0S2U1S0S2U2S0S2U3S1S2A1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition TC1 : axst := ltac2:(tb__ "0|0|
S7S1fA1S1fLx;S4bS2eS0S49S4aS32A1S1S49A1A3A2S1fR1LX;S2eX7x2").
Lemma TC1_eq : ltac2:(tb__ "0|0|
S26S7S1fA1S4bS2eS0S49S4aS32A1S1S49A1A3A2SaS1fS2dA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition KEPTC : list sobj := ltac2:(tb__ "0|0|
S0SdS65S0SdS5fS0SdS60S63A1S0SdS62S5cS5bS5dS5eA4S0SdS61S0SdS68S0SdS50S0SdS51S0SdS73S1SdA1A3A3A3A3A3A3A3A3A3").
Definition RESTC : list sobj := skipn 9 (ss_objs (ax_S TC1)).
Lemma TC1_objs : ltac2:(tb__ "0|0|
S26S5SdA1S16S1eS2dA1A1S9SdS30S36A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition TC2 : axst := ltac2:(tb__ "0|0|
S23S2dS7fS1eS2dA1S30A2A2").
Definition TC4 : axst := ltac2:(tb__ "0|0|
S6eS31S4fS67A1A2").
Definition RCr : axst := ltac2:(tb__ "0|1|
S59S3dS0S8S2SeA2M0S3S2SeU14S5aA4S0G0S3S2SeU1S15S54A1A4S1G0A1A3A3S5cS5bS5dS5eS0SdS73S1SdA1A3S4fS67A1A8").
Lemma TC4_ent : ltac2:(tb__ "0|0|
S26S4S47S37S29S53A3S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma TC4_below : ltac2:(tb__ "0|0|
S26S4S6aSfS14S10S1eS31A1A1A1S4fS67A1A3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition runCr : list leafA := ltac2:(tb__ "0|0|
S74UaS0S3fS54S1S3fA1A3S29A3").
Lemma runCr_eq : ltac2:(tb__ "0|0|
S26S5S20A1S74UaS0S3fS54S1S3fA1A3S29A3S34A3"). Proof. unfold runCr. reflexivity. Qed.
Lemma chkCrM : ltac2:(tb__ "0|1|
S26S4S46S10S1eS29A1A1S34S0S8S1fS45A2M0S3S1fS45S55S53A4S1G0A1A3A3S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma nxRCr : ltac2:(tb__ "0|1|
S27S26S4S1bS1eS29A1M0A1SbA3S76S72S10G0A1A2A2"). Proof. split; [reflexivity | unfold Pos.le; cbn; discriminate]. Qed.

Lemma QC_sumS : ltac2:(tb__ "0|1|
S79OF_;S41S11S5S4eQ40A1A1S44S3aR4R3A3S43S3aS10S1eS3bA1A1M0R4A3S78S3aR6S40S3aR5S3bR4R3A5S42S3aR5G0R4R3S2bA6A4F_;F_;Ftp;Frho;FJx;Fok;").
Proof.
  intros ok Jx rho tp HOK HST. rewrite (proj1 preQC_nx) in *.
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (JQ_LQA1 Jx NPRE rho tp PostQC w Hw) | exact (seg_QC_sound Jx ok rho tp HOK HST)].
Qed.
Lemma QC_sumC : ltac2:(tb__ "0|1|
S41S11S5S4eQ40A1A1S43S3aS10S1eS3bA1A1M0R3A3S77S3aS40S3aR4S3bR3R2A5S42S3aR4G0R3R2S2bA6A3F_;Ftp;Frho;FJx;").
Proof.
  intros Jx rho tp HST. rewrite (proj1 preQC_nx) in *.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (JQ_LQA1 Jx NPRE rho tp PostQC w Hw) | exact (seg_QC_complete Jx rho tp HST)].
Qed.

Section TR.
Context {Q : assn} (X : trk Q).
Theorem seg_D_CrM : ltac2:(tb__ "0|1|
S41S11S5S4eQ40A1A1S4dVQ;VX;R3A3S1fS45S11S6bS8S1fS45A2M0S3S1fS45R3R2A4S0G0S3S1fS45S55S53A4S1G0A1A3A3S48R3R7R2A3S4cVQ;VX;S40S3aR9R5R3R7A5A3F_;F_;Frho';FM;FT;S4cVQ;VX;S40S3aR5S29R4R3A5A3F_;F_;Ftp;Frho;FJ;").
Proof. intros J rho tp HJ HC. exact (tr_piece X 10%nat _ RCr runCr [(RC, MC)] runCr_eq chkCrM (proj1 nxRCr) (proj2 nxRCr) J rho tp HJ HC). Qed.
Theorem qc_call : ltac2:(tb__ "0|0|
S41S11S5S4eQ40A1A1S4dVQ;VX;R3A3S11S19S10S1eS28A1A1R4R1A3S4cVQ;VX;S40S3aR6S2eR2R4A5A3F_;Frho';S4cVQ;VX;S40S3aR5S28R4R3A5A3F_;F_;Ftp;FrhoE;FJ;").
Proof.
  intros J rhoE tp HJ HC.
  exact (tr_call X Cqc PreQC PostsQC sC RC0 TQC QC_sumS QC_sumC HeC HchkC HTC FBCC FBTC NXCC J rhoE tp HJ HC).
Qed.
End TR.
End SegQ3D_qc_defs.

(* [comment removed for export] *)
Module SegQ3D_sum.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "qbatch"; "AA"; "aa_q_global"; "aa_q_thread"; "@Corelib.Init.Datatypes"; "list"; "nil"; "app"; "nat"; "prod"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "holds"; "agree_below"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_exit"; "F_T0x"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel"; "A1T"; "rhoT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr"; "TR"; "JOK"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel"; "JRQ"; "HVP"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMax"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "qsize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states"; "KEEP3"; "ReQ3e"; "ReQ3n"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "JQ3"; "QW"; "sec_foot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece"; "keeps"; "@Stdlib.Lists.List"; "In"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv"; "JRD"; "JRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_loop"; "QC_step"; "QI_step"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM"; "PreR2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states"; "PM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post"; "PostsQ3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep"; "hd_addr"; "last_addr"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_exit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section RecSum.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.
Variables (A : AA) (rho : valuation) (tp : list word).
Hypothesis HTL : aa_q_thread A <> [].
Hypothesis HCI : aa_cache_inited A = true.
Hypothesis HBND : qbounded A.
Context {Q : assn} (X : trk Q).
Hypothesis HQ : ltac2:(tb__ "0|0|
S1cS2bSaS1fVrho;Vtp;S32VK;VA;A2R1A6VQ;R2A1F_;Fw;").
Hypothesis HJQ : ltac2:(tb__ "0|1|
S1S4S0A1M0G0S16VQ;VX;S18VK;VA;Vrho;R3R2R1A6A3Frest;Fpre;FA1;").
Hypothesis HJD : ltac2:(tb__ "0|1|
S1S4S0A1M0G0S16VQ;VX;S2cVK;VA;Vrho;R3R2R1A6A3Frest;Ftmp;FA1;").
Hypothesis HJI : ltac2:(tb__ "0|1|
S1S9S9S7S4S8S9S9A2A1S4S0A1M0G0S16VQ;VX;S2dVK;VA;Vrho;R7R6R5R4R3R2R1AaA3Frest;Ftmp;Fits;Fnd;Fn0;Fa;FA1;").
Let TPI : list word -> Prop := fun _ => True.
Let all : list qbatch := ltac2:(tb__ "0|0|
S6S0S2VA;A1S3VA;A1A3").

Definition PM_step : Prop := ltac2:(tb__ "0|0|
S17SbSdVrho;A1S12A3S28S1dS1eVall;A1A2ScS19R1Vall;A2S15VQ;VX;S10SaS18VK;VA;Vrho;S13VA;A1S5S0A1Vall;A6S31R2Vtp;A5A3F_;Frho';F_;F_;").
Hypothesis HQI : ltac2:(tb__ "0|0|
S4S0A1S2fVK;VA;Vrho;VQ;VX;R1VTPI;A7Frest;").
Hypothesis HQC : ltac2:(tb__ "0|0|
S4S0A1S2eVK;VA;Vrho;VQ;VX;R1VTPI;A7Frest;").
Hypothesis HPM : PM_step.

Lemma QW_A1T : ltac2:(tb__ "0|0|
S9S24S13VA;A1R1A2S24VA;R2A2F_;Fz;").
Proof.
  intros z [H|H]; [left | right; exact H]. unfold A1T in H.
  apply (proj1 (qzone_perm A [] (aa_q_global A ++ aa_q_thread A) z ltac:(unfold qall; cbn [app]; apply Permutation_app_comm))). exact H.
Qed.

Lemma SF_A1T : ltac2:(tb__ "0|0|
S9S25S13VA;A1R1A2S25VA;R2A2F_;Fz;").
Proof.
  intros z. apply sec_foot_mono; [reflexivity | intros y Hy; exact Hy |]. unfold A1T, qall. cbn [aa_q_thread aa_q_global set_q app].
  intros y Hy. rewrite qitems_app in *. apply in_app_or in Hy. apply in_or_app. tauto.
Qed.

Lemma rec_core : ltac2:(tb__ "0|0|
ScS17SbSdVrho;A1S12A3S19R2Vall;A2S28S1dS1eVall;A1A2S15VQ;VX;S10SaS18VK;VA;Vrho;S13VA;A1S5S0A1Vall;A6S30R4Vtp;A5A3F_;F_;F_;Frho2;").
Proof.
  intros rho2 HF0 HVp HGT.
  assert (HSZ : qsize all < 2 ^ 62).
  { unfold all. rewrite qsize_app. destruct HBND as [B1 B2]. unfold kQuarantineMax in B2. lia. }
  assert (NE : all <> []) by (unfold all; intros E; apply app_eq_nil in E as [_ E]; exact (HTL E)).
  apply (recycle_deq K HL A rho (A1T A) eq_refl HCI QW_A1T X (HJQ _) tp HSZ); [| exact (HPM HF0) | exact NE | exact HGT | exact HVp].
  intros tmp rest' rho3 NEt HG HS HV. change (aa_q_global (A1T A)) with all in HG.
  apply (tr_pure X _ (0 <= qsize rest')).
  { intros [tr [ms md]] Hw. destruct (proj2 Hw) as (HK & (HBM & _) & _). cbn [w_tr w_cfg cfg_model fst snd] in HK, HBM.
    pose proof (benv_of_K K HL (A1T A) HCI rho3 tp tr md HK) as BE. pose proof (proj1 (be_qp _ _ BE)) as HBP. rewrite (qall_A1 (A1T A) eq_refl) in HBP.
    change (aa_q_global (A1T A)) with all in HBP. rewrite HG in HBP. apply Forall_app in HBP as [_ P2]. apply Forall_app in HBM as [_ M2].
    pose proof (qsize_ge (A1T A) _ rest' P2 M2) as Q2. unfold kQuarantineBatchSize in Q2. lia. }
  intros HR0.
  apply (dorecycle_xg K HL A rho X HJD HJI rest' TPI (HQI rest') (HQC rest')); [| exact I | exact NEt | | | exact HV].
  - intros A' rho4 tp4 HTP (I1 & I2 & I3 & I4 & I5 & I6) E208.
    eapply (tr_conseq X); [|apply (tr_done X); exact HQ]. intros w Hw.
    apply (exit_R K HL A rho A' rest' rho4 tp tp4 w I1 I2 I3 I4 I5); [| exact E208 | exact HF0 | exact Hw].
    unfold kQuarantineMin, kQuarantineMax in *. lia.
  - split; [reflexivity|]. split; [exact HCI|]. split; [exact QW_A1T|]. split; [apply QP_refl_q|]. split; [exact HG | exact SF_A1T].
  - rewrite HG, qsize_app in HSZ. lia.
Qed.

Lemma F0x_of : ltac2:(tb__ "0|0|
S2aScS1cS11SeS1fVrho;R3A3S10SaR2R5R4Vtp;R3A6SbS27SbR1S12A3S27SbR2SfS29R8A1A1A3F_;Ff;S17SbSdVrho;A1S12A3F_;F_;F_;FJ;Fw;Frho';FSt;").
Proof.
  intros St rho' w J Hag Hw HIN. pose proof (SPA_facts_hold segsA _ rho' St tp w Hw) as HFa. apply Forall_forall. intros f Hf.
  apply (holds_agree_vals NPRE rho rho' f (agree_below_vals _ _ _ Hag) (proj1 (forallb_forall _ _) F_T0x_below f Hf)).
  exact (proj1 (Forall_forall _ _) HFa f (HIN f Hf)).
Qed.

Theorem recycle_sum_n : ltac2:(tb__ "0|1|
S1bS1aS4S0A1S2VA;A1M0S5S0A1A3A1ScS26S20S14VA;S33G0A1S34G0A1Vrho;A4R1A3S15VQ;VX;S10SaS23SaVK;VA;A3S22R2Vtp;A5A3F_;Frho';F_;").
Proof.
  intros HGL rho' HKp.
  destruct (rhoT_vals A (hd_addr (aa_q_global A)) (last_addr (aa_q_global A)) rho) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RAG).
  apply (tr_pure X _ (Forall (holds rho) F_T0x)).
  { intros w Hw. apply (F0x_of ReQ3n rho' w _ (agree_below_trans _ _ _ _ RAG (proj1 HKp)) Hw). intros f Hf. unfold F_T0x in Hf. cbn [In] in Hf.
    unfold ReQ3n, mkPost3; cbn [ax_S mkA ss_facts]. apply in_or_app; left. unfold F_Tn. apply in_or_app; left. unfold F_T0. apply in_or_app. right. cbn [In]. tauto. }
  intros HF0.
  apply (tr_glue X _ (JRQ K A rho (A1T A) [] all) PreR2 tp (fun r => HVP r all /\ kQuarantineMax < qsize all)).
  - intros w Hw. exact (entry_Rn K HL A rho rho' tp w HTL HGL HCI HBND HKp Hw).
  - intros r [R1 R2]. exact (rec_core r HF0 R1 R2).
Qed.

Theorem recycle_sum_e : ltac2:(tb__ "0|0|
S1aS4S0A1S2VA;A1S5S0A1A3S9S9ScS26S20S14VA;R3R2Vrho;A4R1A3S15VQ;VX;S10SaS23SaVK;VA;A3S21R2Vtp;A5A3F_;Frho';Fgb;Fgf;F_;").
Proof.
  intros HGL gf gb rho' HKp.
  destruct (rhoT_vals A gf gb rho) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RAG).
  apply (tr_pure X _ (Forall (holds rho) F_T0x)).
  { intros w Hw. apply (F0x_of ReQ3e rho' w _ (agree_below_trans _ _ _ _ RAG (proj1 HKp)) Hw). intros f Hf. unfold F_T0x in Hf. cbn [In] in Hf.
    unfold ReQ3e, mkPost3; cbn [ax_S mkA ss_facts]. apply in_or_app; left. unfold F_T. apply in_or_app; left. unfold F_T0. apply in_or_app. right. cbn [In]. tauto. }
  intros HF0.
  apply (tr_glue X _ (JRQ K A rho (A1T A) [] all) PreR2 tp (fun r => HVP r all /\ kQuarantineMax < qsize all)).
  - intros w Hw. exact (entry_Re K HL A gf gb rho rho' tp w HTL HGL HCI HBND HKp Hw).
  - intros r [R1 R2]. exact (rec_core r HF0 R1 R2).
Qed.
End RecSum.
End SegQ3D_sum.

(* [comment removed for export] *)
Module SegQ3D_qi_arith.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SLit"; "SPUle"; "SVar"; "rw"; "SPAlign"; "SPBranch"; "SPUlt"; "SPNot"; "SAlu"; "SExt"; "holds"; "@Corelib.Init.Logic"; "and"; "eq"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "snd"; "app"; "true"; "fst"; "length"; "list"; "negb"; "prod"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "modulo"; "mul"; "pow"; "div"; "of_nat"; "sub"; "eqb"; "lt"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "max_count"; "Size"; "kUserSpaceSize"; "rz"; "is_primary"; "kSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "cs_allocated_user"; "aa_geom"; "ag_spacebeg"; "cs_cache"; "cs_mapped_user"; "ag_ctx"; "ag_thread"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "BC_GE"; "ALU_AND"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith"; "FQ_mag"; "vb_of"; "FQ_geo"; "FQ_it"; "FQ_stk"; "QIV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "it_ab"; "it_cls"; "qall"; "qitems"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs"; "SIDEQ"; "factsQ"; "sQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states"; "spD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "cls_of"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition FQ_stk : list sprop := ltac2:(tb__ "0|1|
SeS0S2S1Z7fff7f800000A1S26S47S26S3PfA1S1Zc0A1A2M0A2A2SeS0S6S35S1N400A1G0A3SeS0S6S35G0S1N10000000000A1A3S10S0A1A3A3A3").
Definition FQ_geo : list sprop := ltac2:(tb__ "0|5|
SeS0S7S1Z0A1S1Z1A1A2SeS0S2S1Z1000A1M0S3P97M1A1M2A2SeS0S2G2S1Z7fffff7ff000A1M3A2SeS0S5G1ZcA2SeS0S2G0S3P98A1M4A2SeS0S2G4G3A2S10S0A1A3A3A3A3A3A3").
Definition FQ_it : list sprop := ltac2:(tb__ "0|10|
SeS0S5Pa5M0Z4M1A2SeS0S5P9bM2Z10M3A2SeS0S2S1Z10007fff8000A1S3G2A1M4A2SeS0S2G4S1Z7fdfff7ff000A1A2SeS0S6S34S3P9cA1S26G4S1Z2000000000A1A2M5A3SeS0S2S1Z1A1S3Pc8A1M6A2SeS0S2G6S1Z1eA1A2SeS0S2S1G3A1M7S3Pc9M8A1M9A2SeS0S2G9S1Z10000A1A2SeS0S5G8G1A2SeS0S2G4S3G0A1MaA2SeS0S7GaG5A2SeS0S8S6S37S9S36SaS13Q20S3PcbA1A3S1ZffA1A3S1Z3MbA1A3A1SeS0S8S6S34S3PcfA1McS1Z0A1A3A1SeS0S7S3PceA1GcA2SeS0S2GcS1Z100A1A2SeS0S2S1Z8A1S3PcdMdA1MeA2SeS0S2GeS1Z10000000000A1A2SeS0S5GdGbA2SeS0S2S26S26GaG7A2GeA2MfG5A2SeS0S2GfS1Z7fffff800000A1A2S10S0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition FQ_mag : list sprop := ltac2:(tb__ "0|2|
SeS0S5Pd2M0Z4A2SeS0S2S3P9bA1S3G0A1M1A2SeS0S7G1S3Pa5A1A2S10S0A1A3A3A3").
Lemma factsQ_eq : ltac2:(tb__ "0|1|
SfSdS16S0A1M0S45R1A1S12S0S3cS12S0S3aS12S0S3bSfG0Lvb;R1S38S10S0A1Xfx2A3A3A3A3Fvb;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition QIV (rho : valuation) (it : Z * Z) (cs : class_state) (t st : Z) : Prop := ltac2:(tb__ "0|4|
S14S19S19Vit;A3S19S11S19S19Vit;A3S19S3fVit;A1S19ScSdS25Q40M0A1M1S4Vrho;Pa5A2S24G0S21R3Z10A2A2A3ScSdG1S4Vrho;Pc8A2S24G0R1A2A3ScSdG1S4Vrho;Pc9A2S24G0S28R1A1A2A3ScSdG1S4Vrho;PcaA2S24G0S31Vcs;A1A2A3ScSdG1S4Vrho;PcbA2S24G0S1bS1bZ3S1dZ100Vt;A2A2S1dZ10000S1fR2S1eZ2Z20A2M2A2A2A2A2A3ScSdG1S4Vrho;PccA2S24G0S1cR2G2A2A2A3ScSdG1S4Vrho;PcdA2S24G0S1dS1fS1bR2Z7A2Z8M3A2G3A2A2A3ScSdG1S4Vrho;PceA2S24G0S20S15S19S30Vcs;A1A2A1A2A3ScSdG1S4Vrho;PcfA2S24G0S27R1A1A2A3ScSdG1S4Vrho;Pd1A2S24G0Vst;A2A3SdG1S4Vrho;Pd2A2S24G0S3eVit;A1A2A3A2A2A2A2A2A2A2A2A2A2Tc;Tn;Tu;").

Definition vb_of (it : Z * Z) : bool := ltac2:(tb__ "0|0|
S17S22S2aS11S19S19Vit;A3A1Z10A2A1").

Lemma max_count_facts : ltac2:(tb__ "0|2|
S19ScS1aZ1M0R1A2S1aR1Z1eA2A2ScS1aG0S27R2A1M1A2S1aG1Z100A2A2F_;Fc;").
Proof.
  assert (H : forallb (fun c => (1 <=? max_count c) && (max_count c <=? 256)) (zseq 1 30) = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  intros c Hc. pose proof (range_check _ 1 30 H c ltac:(lia)) as X. apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. lia.
Qed.

Section Arith.
Variable A : AA.
Hypothesis HG : geom_ok (aa_geom A).
Hypothesis HQP : q_pure A.
Hypothesis HAU : ltac2:(tb__ "0|1|
S19ScS1aZ1R1A2S1aR1Z1eA2A2ScS1aZ0S2dS48VA;R2A2A1M0A2S1aG0S29A2A2F_;Fc;").
Variables (rho : valuation) (it : Z * Z) (t st : Z).
Hypothesis HIN : ltac2:(tb__ "0|0|
S49S18S19S19A2Vit;S41S40VA;A1A1A3").
Hypothesis HPR : ltac2:(tb__ "0|0|
SdSfS2bS11S19S19Vit;A3A1S13A3").
Let c := it_cls it.
Let cs := cls_of A c.
Hypothesis HMU : ltac2:(tb__ "0|1|
ScS1aS2dVcs;A1S31Vcs;A1M0A2S1aG0S29A2A2").
Hypothesis HNF : ltac2:(tb__ "0|0|
S23S20S15S19S30Vcs;A1A2A1S27Vc;A1A2").
Hypothesis Ht : 0 <= t < 256.
Hypothesis HRIG : ltac2:(tb__ "0|4|
ScSdS25Q40M0A1M1S4Vrho;P97A2S24G0S33S2eVA;A1M2A1A2A3ScSdG1S4Vrho;P98A2S24G0S32G2A1A2A3ScSdG1S4Vrho;P9bA2S24G0S2fG2A1M3A2A3SdG1S4Vrho;P9cA2S24G0S1bG3S2cA2A2A3A2A2A2").
Hypothesis HV : ltac2:(tb__ "0|0|
S3dVrho;Vit;Vcs;Vt;Vst;A5").

Lemma qi_geo_facts : Forall (holds rho) FQ_geo.
Proof.
  destruct HRIG as (E151 & E152 & _ & _). pose proof (topG_range (aa_geom A)) as TG.
  pose proof (geom_old _ HG) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & _).
  unfold FQ_geo. repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E151, ?E152, ?u64_lit by lia; try lia.
Qed.

Lemma qi_geom : ltac2:(tb__ "0|c|
S14S19S19Vit;A3S19S11S19S19Vit;A3S19S28Vc;A1S19S3eVit;A1S19S2fS2eVA;A1A1S19ScScS1aZ1M0Vc;A2S1aVc;Z1eA2A2ScScS1aZ10M1R3A2S1aR3Z10000A2A2ScSdS19S1cR3G1A2Z0M2A3ScScS1aG1S2aR4A1M3A2S1aG3Z800A2A2ScSdS19S1cG3G1A2G2A3ScSdS19R5S1bR2G3A2A3ScScS1aG0R4A2S1aR4Zfc00M4A2A2ScS1aS1bR1S1dVc;S1eZ2M5Z20A2A2A2M6R2A2ScSdS19S1cS21R2G6A2M7R3A2G2A3ScS1aS1bG7R3A2S2dVcs;A1A2ScSdS19S1cR2G1A2G2A3ScS1aS1bR5S1dS1fS1bR4Z7A2Z8M8A2G8A2M9A2S1bR2R3A2MaA2ScS1aGaS1bR1S1eG5Z25A2A2MbA2ScSdS19S1cR1S1eG5G1A2A2G2A3ScS1aZ10007fff8000R1A2ScS1aS1bGbZ1000A2Z7fffff800000A2ScScS1aG8G9A2S1aG9G4A2A2SdS19S1cG9G8A2G2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2TSB;Tab;TS;Tn;Tu;").
Proof.
  cbv zeta. pose proof (item_slot A HQP HAU HG it HIN HPR) as IS. cbv zeta in IS. fold c in IS.
  destruct IS as (C1 & R1 & M1 & U1 & A16 & Z1 & Z2 & RZ & RZ16 & EU & UN & N1 & HS & TOP).
  pose proof (SB_facts A HG) as (S1 & S2 & S3). rewrite kSpaceSize_val in *. unfold HIGH_SHADOW_END in *.
  assert (IP : item_pure A it).
  { destruct (qitems_In A it HIN) as (b & Hb & Hib). destruct HQP as [HBP _]. pose proof (proj1 (Forall_forall _ _) HBP b Hb) as (_ & _ & _ & HF).
    exact (proj1 (Forall_forall _ _) HF it Hib). }
  destruct IP as (_ & _ & IPP & _). specialize (IPP HPR). cbv zeta in IPP. fold c cs in IPP. unfold region_beg, kRegionSize in IPP. unfold it_ab in *.
  pose proof (Z.div_mod (snd it + 7) 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound (snd it + 7) 8 ltac:(lia)) as B8.
  assert (R8 : (fst it - rz (snd it) + Size c - fst it) mod 8 = 0).
  { replace (fst it - rz (snd it) + Size c - fst it) with (Size c - rz (snd it)) by lia.
    pose proof (Z.div_mod (Size c) 16 ltac:(lia)) as DS. pose proof (Z.div_mod (rz (snd it)) 16 ltac:(lia)) as DR. rewrite Z2 in DS. rewrite RZ16 in DR.
    rewrite DS, DR. replace (16 * (Size c / 16) + 0 - (16 * (rz (snd it) / 16) + 0)) with ((2 * (Size c / 16) - 2 * (rz (snd it) / 16)) * 8) by lia. apply Z.mod_mul. lia. }
  pose proof (Z.div_mod (fst it - rz (snd it) + Size c - fst it) 8 ltac:(lia)) as DQ. rewrite R8 in DQ.
  assert (N8LE : (snd it + 7) / 8 * 8 <= fst it - rz (snd it) + Size c - fst it).
  { assert ((snd it + 7) / 8 <= (fst it - rz (snd it) + Size c - fst it) / 8); [|lia]. apply Z.div_le_lower_bound; [lia|]. lia. }
  repeat split; try lia.
  destruct IPP as (P1 & P2 & P3). unfold cs, c, it_cls in *. lia.
Qed.

Lemma qi_it_facts : Forall (holds rho) FQ_it.
Proof.
  destruct HRIG as (E151 & E152 & E155 & E156). destruct HV as (E165 & E200 & E201 & E202 & E203 & E204 & E205 & E206 & E207 & E209 & E210).
  pose proof qi_geom as GEO. cbv zeta in GEO. fold c cs in E200, E201, E202, E206, E207.
  destruct GEO as (C1 & Z1 & Z2 & RZ & RZ16 & EU & N1 & R1 & M1 & U1 & A16 & UN & TOP & S1 & S2 & S3 & N8a & N8b).
  pose proof (max_count_facts c C1) as MC. rewrite kSpaceSize_val in E156.
  assert (M16 : (fst it - 16) mod 16 = 0).
  { rewrite EU. pose proof (Z.div_mod (it_ab it) 16 ltac:(lia)) as DA. pose proof (Z.div_mod (rz (snd it)) 16 ltac:(lia)) as DR. rewrite A16 in DA. rewrite RZ16 in DR.
    rewrite DA, DR. replace (16 * (it_ab it / 16) + 0 + (16 * (rz (snd it) / 16) + 0) - 16) with ((it_ab it / 16 + rz (snd it) / 16 - 1) * 16) by lia. apply Z.mod_mul. lia. }
  assert (N0 : snd it / 2 ^ 32 = 0) by (apply Z.div_small; lia).
  assert (EM : eval rho (add (SVar 165) (SLit 16)) = Z_to_bv 64 (fst it)).
  { pose proof (eval_add_lit A rho (SVar 165) (fst it - 16) 16 E165 ltac:(lia) ltac:(lia) ltac:(lia)) as X. replace (fst it - 16 + 16) with (fst it) in X by lia. exact X. }
  assert (EMN : eval rho (add (add (SVar 165) (SLit 16)) (SVar 205)) = Z_to_bv 64 (fst it + (snd it + 7) / 8 * 8)) by (apply eval_add_z; [exact EM | cbn [eval]; exact E205 | lia | lia | lia]).
  assert (ESK : eval rho (add (SVar 155) (SLit 137438953472)) = Z_to_bv 64 (ag_spacebeg (aa_geom A) + 137438953472)) by (apply (eval_add_lit A); try lia; cbn [eval]; exact E155).
  unfold FQ_it. repeat apply Forall_cons; try apply Forall_nil.
  - cbn [holds]. split; [lia|]. rewrite E165, u64_lit by lia. exact M16.
  - cbn [holds]. split; [lia|]. rewrite E155, u64_lit by lia. exact S1.
  - cbn [holds eval]. rewrite E155, !u64_lit by lia. lia.
  - cbn [holds eval]. rewrite E155, !u64_lit by lia. lia.
  - cbn [holds branch_taken]. rewrite ESK. cbn [eval]. rewrite E156. unfold bv_eqb. apply Z.eqb_eq. reflexivity.
  - cbn [holds eval]. rewrite E200, !u64_lit by lia. lia.
  - cbn [holds eval]. rewrite E200, !u64_lit by lia. lia.
  - cbn [holds eval]. rewrite E201, !u64_lit by lia. lia.
  - cbn [holds eval]. rewrite E201, !u64_lit by lia. lia.
  - cbn [holds]. split; [lia|]. rewrite E201, u64_lit by lia. exact Z2.
  - cbn [holds eval]. rewrite E155, E165, !u64_lit by lia. lia.
  - cbn [holds]. rewrite ESK. cbn [eval]. rewrite E165, !u64_lit by lia. lia.
  - cbn [holds branch_taken]. intros HB. apply negb_true_iff in HB. unfold bv_eqb in HB. apply Z.eqb_neq in HB. apply HB. clear HB.
    rewrite U_and2, U_sext_e by lia. cbn [eval]. rewrite E203, N0, !u64_lit by lia. change (Z.of_N 32) with 32.
    rewrite (Z.mod_small (3 + 256 * t + 65536 * 0) (2 ^ 32)) by lia. unfold CursorGlue.zsext. replace (3 + 256 * t + 65536 * 0 <? 2 ^ (32 - 1)) with true by (symmetry; apply Z.ltb_lt; lia).
    change 255 with (Z.ones 8). rewrite Z.land_ones by lia. replace (3 + 256 * t + 65536 * 0) with (3 + t * 2 ^ 8) by lia. rewrite Z.mod_add by lia. reflexivity.
  - cbn [holds branch_taken eval]. rewrite E207. intros HB. unfold bv_eqb in HB. apply Z.eqb_eq in HB. rewrite !u64_lit in HB by lia. lia.
  - cbn [holds eval]. rewrite E206, E207, !u64_lit by lia. exact HNF.
  - cbn [holds eval]. rewrite E207, !u64_lit by lia. lia.
  - cbn [holds eval]. rewrite E205, !u64_lit by lia. lia.
  - cbn [holds eval]. rewrite E205, !u64_lit by lia. lia.
  - cbn [holds]. split; [lia|]. rewrite E205, u64_lit by lia. exact N8b.
  - cbn [holds]. rewrite EMN, ESK, !u64_lit by lia. lia.
  - cbn [holds]. rewrite EMN. cbn [eval]. rewrite !u64_lit by lia. lia.
Qed.

Lemma qi_mag_facts : ltac2:(tb__ "0|0|
SdSfS39Vit;A1S13A3S42S0SbVrho;A1S38A3F_;").
Proof.
  intros HVB. destruct HRIG as (E151 & E152 & E155 & E156). destruct HV as (E165 & E200 & E201 & E202 & E203 & E204 & E205 & E206 & E207 & E209 & E210).
  pose proof qi_geom as GEO. cbv zeta in GEO.
  destruct GEO as (C1 & Z1 & Z2 & RZ & RZ16 & EU & N1 & R1 & M1 & U1 & A16 & UN & TOP & S1 & S2 & S3 & N8a & N8b).
  unfold vb_of in HVB. apply negb_true_iff in HVB. apply Z.eqb_neq in HVB.
  assert (RZ32 : 32 <= rz (snd it)).
  { pose proof (Z.div_mod (rz (snd it)) 16 ltac:(lia)) as DR. rewrite RZ16 in DR. lia. }
  unfold FQ_mag. repeat apply Forall_cons; try apply Forall_nil.
  - cbn [holds]. split; [lia|]. rewrite E210, u64_lit by lia. exact A16.
  - cbn [holds eval]. rewrite E155, E210, !u64_lit by lia. lia.
  - cbn [holds eval]. rewrite E165, E210, !u64_lit by lia. lia.
Qed.

Lemma qi_side : ltac2:(tb__ "0|1|
S44S39Vit;A1M0S43Vrho;S46G0A1A2A2").
Proof.
  destruct HRIG as (E151 & E152 & E155 & E156). destruct HV as (E165 & E200 & E201 & E202 & E203 & E204 & E205 & E206 & E207 & E209 & E210).
  pose proof qi_geom as GEO. cbv zeta in GEO. fold c cs in E200, E201, E202, E206, E207.
  destruct GEO as (C1 & Z1 & Z2 & RZ & RZ16 & EU & N1 & R1 & M1 & U1 & A16 & UN & TOP & S1 & S2 & S3 & N8a & N8b).
  assert (N0 : snd it / 2 ^ 32 = 0) by (apply Z.div_small; lia). assert (NM : snd it mod 2 ^ 32 = snd it) by (apply Z.mod_small; lia).
  rewrite N0 in E203. rewrite NM in E204.
  set (x := (it_ab it - (ag_spacebeg (aa_geom A) + c * 2 ^ 32)) / Size c).
  assert (EX : it_ab it - (ag_spacebeg (aa_geom A) + c * 2 ^ 32) = Size c * x).
  { unfold x. pose proof (Z.div_mod (it_ab it - (ag_spacebeg (aa_geom A) + c * 2 ^ 32)) (Size c) ltac:(lia)) as D. rewrite M1 in D. lia. }
  assert (X0 : 0 <= x) by (unfold x; apply Z.div_pos; lia).
  assert (M16 : (fst it - 16) mod 16 = 0).
  { rewrite EU. pose proof (Z.div_mod (it_ab it) 16 ltac:(lia)) as DA. pose proof (Z.div_mod (rz (snd it)) 16 ltac:(lia)) as DR. rewrite A16 in DA. rewrite RZ16 in DR.
    rewrite DA, DR. replace (16 * (it_ab it / 16) + 0 + (16 * (rz (snd it) / 16) + 0) - 16) with ((it_ab it / 16 + rz (snd it) / 16 - 1) * 16) by lia. apply Z.mod_mul. lia. }
  assert (HWD : (3 + 256 * t + 65536 * 0) / 2 ^ 16 = 0) by (apply Z.div_small; lia).
  assert (HWM : (3 + 256 * t + 65536 * 0) mod 256 = 3) by (replace (3 + 256 * t + 65536 * 0) with (3 + t * 256) by lia; rewrite Z.mod_add by lia; reflexivity).
  exists x, (rz (snd it) - 16). destruct (sQ_vals (vb_of it)) as (W13 & W155 & W158 & W148 & W138 & W139 & W141 & W145 & W146).
  unfold QI_side, V_CLS, V_SIZE, ACQ. cbv zeta. cbn [rho_sub rw]. rewrite W13, W155, W158, W148, W138, W139, W141, W145. unfold vIT. cbn [eval].
  assert (KU : kUserSpaceSize = 2 ^ 32 - 2 ^ 29) by reflexivity. unfold HIGH_SHADOW_END.
  rewrite E165, E155, E200, E201, E202, E203, E204, E205. rewrite !u64_lit by (clear -C1 Z1 HMU KU S2 S3 N1 N8a Ht RZ EU R1 TOP UN U1; lia). rewrite HWD, HWM.
  assert (EM : fst it - 16 = ag_spacebeg (aa_geom A) + c * 2 ^ 32 + Size c * x + (rz (snd it) - 16)) by (clear -EU EX; lia).
  assert (DS : rz (snd it) - 16 < Size c) by (clear -EU UN N8a; lia).
  assert (MUB : Size c * x + Size c <= cs_mapped_user cs) by (clear -EX U1 HMU; lia).
  split; [exact C1|]. split; [reflexivity|]. split; [exact X0|]. split; [clear -RZ DS; lia|]. split; [exact EM|]. split; [exact MUB|].
  split; [clear -HMU KU; lia|]. split; [clear -S2; lia|]. split; [clear -EU UN TOP S3 N8a; lia|]. split; [exact M16|].
  split; [clear -Ht; lia|]. split; [clear -N1; lia|]. split; [replace (0 * 2 ^ 32 + snd it + 7) with (snd it + 7) by lia; reflexivity|].
  unfold vb_of in *. destruct (rz (snd it) =? 16) eqn:ERZ; cbn [negb bgv] in *.
  - apply Z.eqb_eq in ERZ. cbn [eval rho_sub rw]. rewrite W13. unfold vIT. cbn [eval]. rewrite E165, u64_lit by (clear -EU R1 S2 S3 TOP UN RZ C1 Z1 N8a; lia). clear -ERZ. lia.
  - unfold vAB. cbn [eval rho_sub rw]. rewrite W146. cbn [eval]. rewrite E210, u64_lit by (clear -R1 S2 S3 TOP Z1 C1; lia). clear -EU. lia.
Qed.
End Arith.
End SegQ3D_qi_arith.

(* [comment removed for export] *)
Module SegQIF_defs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "cons"; "list"; "nil"; "true"; "option"; "pair"; "prod"; "app"; "None"; "Some"; "false"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "sprop"; "ss_next"; "ss_facts"; "valuation"; "sobj"; "SLit"; "rw"; "sprop_below"; "FcsrFrm0"; "agree_below"; "mkSS"; "ss_objs"; "ss_regs"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "la_state"; "ax_X"; "axwf"; "mkLeafA"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQIF_defs"; "CqiP"; "sP"; "RP"; "PostsQIP"; "TQP"; "TQPf"; "factsP"; "objsP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i9.SegQIP_states"; "PreQIP"; "PostQIP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "obj_subst"; "rho_sub"; "sprop_subst_opt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs"; "SIDEQ"; "FRAMEQ"; "renQ"; "sQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "LQA"; "stableA"; "ok_frameA"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr"; "TR"; "JOK"; "@Stdlib.Lists.List"; "In"; "forallb"; "fold_right"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states"; "DQI"; "DQIs"; "vIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states"; "NXR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states"; "optR"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i9.SegQIP_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQIP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Definition objsP (vb : bool) : list sobj := ltac2:(tb__ "0|0|
S3fS14S14S31S37A1S1bS1eS2eVvb;A1A1A1A4").
Definition factsP (vb : bool) : list sprop := ltac2:(tb__ "0|1|
S48S2S10A1M0S10S10G0S5S10A1G0Lx;S33S37R2A2S10S1S10R1R2A3Lg;R1X5x2Lacc;Lf;S3S10A1S12S1eS2eVvb;A1A1A1A5").
Definition CqiP (vb : bool) : axst := ltac2:(tb__ "0|1|
S4fS1aS51S1cS1eS52A1M0A1S4cS18S9SeA1S8S14S2dVvb;A1S36A3S8S10S12G0A1S2cVvb;A1A3S54SbA9S3S7SeSeA2A1A2").

Definition sP (vb : bool) : wsub := ltac2:(tb__ "0|1|
S1S7S25SeA2M0S6S25SeP99S15Z1A1A4S1G0S6S25SeP9aS15Z0A1A4S1G0S6S25SeP94SfPc9A1A4S4dP1S1eS26Vvb;A1A1S1eS2eVvb;A1A1A3A3A3A3").
Definition RP (vb : bool) : list sobj := ltac2:(tb__ "0|0|
S55S41S26Vvb;A1S2eVvb;A1S27Vvb;A1A3A1").
Definition PostsQIP (vb : bool) : list leafA := ltac2:(tb__ "0|0|
S1S1fS24S2fVvb;A1S4eA2S3S1fA1A3").
Definition TQP (vb : bool) : axst := ltac2:(tb__ "0|0|
S42S27Vvb;A1S2eVvb;A1S2fVvb;A1S26Vvb;A1S28Vvb;A1A5").
Definition TQPf_of (vb : bool) : axst := ltac2:(tb__ "0|0|
S40S2aVvb;A1S12S1eS26Vvb;A1A1A1A2").
Definition TQPf_a : axst := Eval vm_compute in (TQPf_of false).
Definition TQPf_b : axst := Eval vm_compute in (TQPf_of true).
Definition TQPf (vb : bool) : axst := if vb then TQPf_b else TQPf_a.
Lemma TQPf_eq : ltac2:(tb__ "0|0|
S0ScS20S40S2aR1A1S12S1eS26R1A1A1A1A2S2bR1A1A3Fvb;"). Proof. intros [|]; vmr. Qed.

Lemma CqiP_wf : ltac2:(tb__ "0|2|
S0SdScS0S23S26R1A1M0A1S4A3SdScS0S1dS1eG0A1A1S4A3ScS2S7SeSeA2M1A1S22G0A1S3G1A1A3A2A2Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RP_eq : ltac2:(tb__ "0|0|
S0ScS2S14A1S28R1A1S36A3Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HeP : ltac2:(tb__ "0|1|
S0ScS5S2S14A1M0A1S41S26R1A1S2eR1A1S27R1A1A3SaG0S28R1A1A2A3Fvb;"). Proof. intros [|]; vm_cast_no_check (eq_refl (Some FRAMEQ)). Qed.
Lemma HchkP : ltac2:(tb__ "0|0|
S0ScS0S43S26R1A1S2eR1A1S27R1A1S28R1A1S3fS1fS20S21S29R1A1A4A5S4A3Fvb;"). Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.
Lemma HTP : ltac2:(tb__ "0|0|
S0S1fS46S1fR1S29R2A1A3ScS20S42S27R3A1S2eR3A1S21R2A1S26R3A1S28R3A1A5S2aR3A1A3F_;FP;Fvb;").
Proof. intros vb P [<-|[]]. reflexivity. Qed.
Lemma FBCP : ltac2:(tb__ "0|1|
S0ScS0S47S10S17S11S1eS26R1A1A1M0A1A1S12G0A1A3S4A3Fvb;"). Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.
Lemma FBTP : ltac2:(tb__ "0|0|
S0ScS0S47S10S17S11S1eS2aR1A1A1A1A1S12S1eS26R1A1A1A1A3S4A3Fvb;"). Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.
Lemma NXCP : ltac2:(tb__ "0|0|
S0S56S50S11S1eS26R1A1A1A1A2Fvb;"). Proof. intros vb. unfold Pos.le. cbn. discriminate. Qed.

Lemma sP_vals : ltac2:(tb__ "0|3|
S0SdScSeS30S27R1A1M0PdA2S53A3SdScSeS30G0P9bM1A2SfG1A1A3SdScSeS30G0P9eA2SfPc8A1A3SdScSeS30G0P94A2SfPc9A1A3SdScSeS30G0P8aA2SfPcaA1A3SdScSeS30G0P8bA2SfPcbA1A3SdScSeS30G0P8dA2SfPccA1A3SdScSeS30G0P91A2SfPcdA1A3ScSeS30G0P92M2A2S0SeLvb;R1SfPd2A1SfG2A1X0x2A3A2A2A2A2A2A2A2A2Fvb;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma sP_sQ : ltac2:(tb__ "0|0|
S0S25S46S25R1S1S25PdS1S25P9bS1S25P9eS1S25P94S1S25P8aS1S25P8bS1S25P8dS1S25P91S1S25P92S3S25A1A3A3A3A3A3A3A3A3A3A3ScSeS30S27R3A1R2A2S30S38R3A1R2A2A3F_;Fv;Fvb;").
Proof. intros [|] v Hv; cbn [In] in Hv; repeat (destruct Hv as [<-|Hv]; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]); destruct Hv. Qed.

Lemma SIDEP_ext : ltac2:(tb__ "0|0|
S0S13S13S25S57R1S11S1eS2eR4A1A1A1A2ScS3eQ40A1S16R3R2A2S16R4R2A2A3F_;Fi;S35R4R3A2S35R5R3A2F_;F_;Fr';Fr;Fvb;").
Proof.
  intros vb r r' HE. apply (SIDEQ_ext vb r r'). intros i Hi. apply HE. rewrite (proj1 (proj2 (proj2 (preQIP_wf vb)))). rewrite (proj1 (proj2 (proj2 (preQI_wf vb)))) in Hi. exact Hi.
Qed.
Lemma QIP_sumS : ltac2:(tb__ "0|1|
S0S4bOF_;S3aS13S2S3eQ40A1A1S3dS34R4R3A3S3cS34S11S1eS2eR6A1A1A1R4A3S35R7R4A2S4aS34R7S39S34R6S2eR8A1M0R5R4A5S3bS34R6S11S1eG0A1A1R5R4S29R8A1A6A4F_;F_;F_;Ftp;Frho;FJx;Fok;Fvb;").
Proof.
  intros vb ok Jx rho tp HOK HST (x & d & HS). rewrite (proj1 (proj2 (proj2 (preQIP_wf vb)))) in *.
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (JQ_LQA1 Jx NPRE rho tp (PostQIP vb) w Hw) | exact (seg_QIP_sound_clean vb Jx ok rho tp x d HOK HST HS)].
Qed.
Lemma QIP_sumC : ltac2:(tb__ "0|1|
S0S3aS13S2S3eQ40A1A1S3cS34S11S1eS2eR4A1A1A1R3A3S35R5R3A2S49S34S39S34R5S2eR6A1M0R4R3A5S3bS34R5S11S1eG0A1A1R4R3S29R6A1A6A3F_;F_;Ftp;Frho;FJx;Fvb;").
Proof.
  intros vb Jx rho tp HST (x & d & HS). rewrite (proj1 (proj2 (proj2 (preQIP_wf vb)))) in *.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (JQ_LQA1 Jx NPRE rho tp (PostQIP vb) w Hw) | exact (seg_QIP_complete_clean vb Jx rho tp x d HST HS)].
Qed.

Section CALLP.
Context {Q : assn} (X : trk Q).
Theorem qip_call : ltac2:(tb__ "0|1|
S0S3aS13S2S3eQ40A1A1S45VQ;VX;R3A3S35R5S32R3S27R5A1A2A2S13S19S11S1eS26R7A1M0A1A1R5R1A3S44VQ;VX;S39S34R7S2bR8A1R2R5A5A3F_;Frho';S44VQ;VX;S39S34R6G0R5R4A5A3F_;F_;F_;Ftp;FrhoE;FJ;Fvb;").
Proof.
  intros vb J rhoE tp HJ HS HC.
  apply (tr_callS X (CqiP vb) (PreQIP vb) (PostsQIP vb) (sP vb) (RP vb) (TQP vb) (SIDEQ vb) (SIDEP_ext vb) (QIP_sumS vb) (QIP_sumC vb)
           (HeP vb) (HchkP vb) (HTP vb) (FBCP vb) (FBTP vb) (NXCP vb) J rhoE tp HJ HS).
  intros rho' Hag. rewrite (TQPf_eq vb). exact (HC rho' Hag).
Qed.
End CALLP.
End SegQIF_defs.

(* [comment removed for export] *)
Module F0A_i0A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.F0A_i0A.I0A"; "contF"; "econtF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0A"; "ED_0A_1"; "ED_0A_2"; "Ebg_0A"; "Edr_0A"; "P0_0A"; "TD_0A_1"; "TD_0A_2"; "Xf_0A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymEntail SymFrame SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0A.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section I0A.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 0.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S1fU0S1Vb;VA;VKc;Vrho1;A6").

Definition contF (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : assn) : Prop := ltac2:(tb__ "0|0|
SaS0S0S4SbQ40A1A1S1dVA;R4A2S20Vkeep;Vrho1;R4A3S10Vsegs;Vok;S7Vsegs;VJFi;S5R6VKc;R5A4VE;R4R3A5VQ;A4F_;F_;FtpE;FrhoE;Frho1';FA';").
Definition econtF (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
SaS0S0S4SbQ40A1A1S1dVA;R4A2S20Vkeep;Vrho1;R4A3SfVsegs;S7Vsegs;VJFi;S5R6VKc;R5A4VE;R4R3A5VQ;A3F_;F_;FtpE;FrhoE;Frho1';FA';").

Theorem free_spine_0A : ltac2:(tb__ "0|1|
SeOF_;S11OF_;SaS2S0S0S4SbQ40A1A1S12S3R5A1S9Vsegs;R8S8R6A1A3S1eR6R5A2S1bU0M0S1RbRaR9R8R6S13S18R4AaS1bG0S1RcRbRaR9R7S14S19R5AaScRdRcRbRaR8S15R6A7ScReRdRcRbR9S16R7A7ScRfReRdRcRaS1aR8A7S0S10Vsegs;R10S7Vsegs;VJFi;S6RfReRcA4S17R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_0A rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_0A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0%nat st false Eps_0A C3_0A Ems_0A C4_0A TM0_0A run4_0A RM_0A D3_0A W3_0A EQ3_0A NX3b_0A RUN4_0A L4_0A D4_0A W4_0A EQ4_0A
             HeM_0A HchkM_0A HTM_0A FBM_0A ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_0A.
    apply (f0_s5 0%nat st q_0A false TM_0A Eq_0A EQ_0A TQ0_0A run5_0A RQ_0A NX5_0A RUN5_0A L5_0A AXQ_0A HeQ_0A HchkQ_0A HTQ_0A FBQ_0A
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_0A.
    apply (f0_s6 0%nat st false TQ_0A Edr_0A Xf_0A run6_0A NX6_0A RUN6_0A L6_0A ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1 0%nat st q_0A true exits1_0A Cert1_0A ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_0A in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (f0_s2 0%nat st true S1c_0A_1 C2_0A_1 EfD_0A_1 ED_0A_1 run2_0A_1 D2_0A_1 W2_0A_1 NX2_0A_1 EQ2_0A_1 RUN2_0A_1 L2_0A_1 AXD_0A_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_0A_1 TDr_0A_1 CD_0A Eps_0A Ebg_0A run3_0A AXDr_0A_1 ENTD_0A_1 RUN3_0A L3_0A NX3_0A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 0%nat st true S1c_0A_2 C2_0A_2 EfD_0A_2 ED_0A_2 run2_0A_2 D2_0A_2 W2_0A_2 NX2_0A_2 EQ2_0A_2 RUN2_0A_2 L2_0A_2 AXD_0A_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_0A_2 TDr_0A_2 CD_0A Eps_0A Ebg_0A run3_0A AXDr_0A_2 ENTD_0A_2 RUN3_0A L3_0A NX3_0A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_0A : ltac2:(tb__ "0|1|
SeOF_;SaS2S0S0S4SbQ40A1A1S11OF_;S3R5A1S1eR5R4A2S1cU0M0S1R9R8R7R5S13S18R3A9S1cG0S1RaR9R8R6S14S19R4A9SdRbRaR9R7S15R5A6SdRcRbRaR8S16R6A6SdRdRcRbR9S1aR7A6S0SfVsegs;S7Vsegs;VJFi;S6ReRdRbA4S17R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_0A rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_0A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0%nat st false Eps_0A C3_0A Ems_0A C4_0A TM0_0A run4_0A RM_0A D3_0A W3_0A EQ3_0A NX3b_0A RUN4_0A L4_0A D4_0A W4_0A EQ4_0A
             HeM_0A HchkM_0A HTM_0A FBM_0A A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_0A.
    apply (ef0_s5 0%nat st q_0A false TM_0A Eq_0A EQ_0A TQ0_0A run5_0A RQ_0A NX5_0A RUN5_0A L5_0A AXQ_0A HeQ_0A HchkQ_0A HTQ_0A FBQ_0A
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_0A.
    apply (ef0_s6 0%nat st false TQ_0A Edr_0A Xf_0A run6_0A NX6_0A RUN6_0A L6_0A A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1 0%nat st q_0A true exits1_0A ECert1_0A A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_0A in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (ef0_s2 0%nat st true S1c_0A_1 C2_0A_1 EfD_0A_1 ED_0A_1 run2_0A_1 D2_0A_1 W2_0A_1 NX2_0A_1 EQ2_0A_1 RUN2_0A_1 L2_0A_1 AXD_0A_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_0A_1 TDr_0A_1 CD_0A Eps_0A Ebg_0A run3_0A AXDr_0A_1 ENTD_0A_1 RUN3_0A L3_0A NX3_0A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 0%nat st true S1c_0A_2 C2_0A_2 EfD_0A_2 ED_0A_2 run2_0A_2 D2_0A_2 W2_0A_2 NX2_0A_2 EQ2_0A_2 RUN2_0A_2 L2_0A_2 AXD_0A_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_0A_2 TDr_0A_2 CD_0A Eps_0A Ebg_0A run3_0A AXDr_0A_2 ENTD_0A_2 RUN3_0A L3_0A NX3_0A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
End I0A.
End F0A_i0A.

(* [comment removed for export] *)
Module F0A_i0Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.F0A_i0Be.I0Be"; "contF"; "econtF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Be"; "ED_0Be_1"; "ED_0Be_2"; "Ebg_0Be"; "Edr_0Be"; "P0_0Be"; "TD_0Be_1"; "TD_0Be_2"; "Xf_0Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymEntail SymFrame SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Be.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section I0Be.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 0.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S1fU0S1Vb;VA;VKc;Vrho1;A6").

Definition contF (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : assn) : Prop := ltac2:(tb__ "0|0|
SaS0S0S4SbQ40A1A1S1dVA;R4A2S20Vkeep;Vrho1;R4A3S10Vsegs;Vok;S7Vsegs;VJFi;S5R6VKc;R5A4VE;R4R3A5VQ;A4F_;F_;FtpE;FrhoE;Frho1';FA';").
Definition econtF (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
SaS0S0S4SbQ40A1A1S1dVA;R4A2S20Vkeep;Vrho1;R4A3SfVsegs;S7Vsegs;VJFi;S5R6VKc;R5A4VE;R4R3A5VQ;A3F_;F_;FtpE;FrhoE;Frho1';FA';").

Theorem free_spine_0Be : ltac2:(tb__ "0|1|
SeOF_;S11OF_;SaS2S0S0S4SbQ40A1A1S12S3R5A1S9Vsegs;R8S8R6A1A3S1eR6R5A2S1bU0M0S1RbRaR9R8R6S13S18R4AaS1bG0S1RcRbRaR9R7S14S19R5AaScRdRcRbRaR8S15R6A7ScReRdRcRbR9S16R7A7ScRfReRdRcRaS1aR8A7S0S10Vsegs;R10S7Vsegs;VJFi;S6RfReRcA4S17R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_0Be rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_0Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0%nat st false Eps_0Be C3_0Be Ems_0Be C4_0Be TM0_0Be run4_0Be RM_0Be D3_0Be W3_0Be EQ3_0Be NX3b_0Be RUN4_0Be L4_0Be D4_0Be W4_0Be EQ4_0Be
             HeM_0Be HchkM_0Be HTM_0Be FBM_0Be ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_0Be.
    apply (f0_s5 0%nat st q_0Be false TM_0Be Eq_0Be EQ_0Be TQ0_0Be run5_0Be RQ_0Be NX5_0Be RUN5_0Be L5_0Be AXQ_0Be HeQ_0Be HchkQ_0Be HTQ_0Be FBQ_0Be
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_0Be.
    apply (f0_s6 0%nat st false TQ_0Be Edr_0Be Xf_0Be run6_0Be NX6_0Be RUN6_0Be L6_0Be ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1 0%nat st q_0Be true exits1_0Be Cert1_0Be ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_0Be in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (f0_s2 0%nat st true S1c_0Be_1 C2_0Be_1 EfD_0Be_1 ED_0Be_1 run2_0Be_1 D2_0Be_1 W2_0Be_1 NX2_0Be_1 EQ2_0Be_1 RUN2_0Be_1 L2_0Be_1 AXD_0Be_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_0Be_1 TDr_0Be_1 CD_0Be Eps_0Be Ebg_0Be run3_0Be AXDr_0Be_1 ENTD_0Be_1 RUN3_0Be L3_0Be NX3_0Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 0%nat st true S1c_0Be_2 C2_0Be_2 EfD_0Be_2 ED_0Be_2 run2_0Be_2 D2_0Be_2 W2_0Be_2 NX2_0Be_2 EQ2_0Be_2 RUN2_0Be_2 L2_0Be_2 AXD_0Be_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_0Be_2 TDr_0Be_2 CD_0Be Eps_0Be Ebg_0Be run3_0Be AXDr_0Be_2 ENTD_0Be_2 RUN3_0Be L3_0Be NX3_0Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_0Be : ltac2:(tb__ "0|1|
SeOF_;SaS2S0S0S4SbQ40A1A1S11OF_;S3R5A1S1eR5R4A2S1cU0M0S1R9R8R7R5S13S18R3A9S1cG0S1RaR9R8R6S14S19R4A9SdRbRaR9R7S15R5A6SdRcRbRaR8S16R6A6SdRdRcRbR9S1aR7A6S0SfVsegs;S7Vsegs;VJFi;S6ReRdRbA4S17R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_0Be rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_0Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0%nat st false Eps_0Be C3_0Be Ems_0Be C4_0Be TM0_0Be run4_0Be RM_0Be D3_0Be W3_0Be EQ3_0Be NX3b_0Be RUN4_0Be L4_0Be D4_0Be W4_0Be EQ4_0Be
             HeM_0Be HchkM_0Be HTM_0Be FBM_0Be A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_0Be.
    apply (ef0_s5 0%nat st q_0Be false TM_0Be Eq_0Be EQ_0Be TQ0_0Be run5_0Be RQ_0Be NX5_0Be RUN5_0Be L5_0Be AXQ_0Be HeQ_0Be HchkQ_0Be HTQ_0Be FBQ_0Be
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_0Be.
    apply (ef0_s6 0%nat st false TQ_0Be Edr_0Be Xf_0Be run6_0Be NX6_0Be RUN6_0Be L6_0Be A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1 0%nat st q_0Be true exits1_0Be ECert1_0Be A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_0Be in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (ef0_s2 0%nat st true S1c_0Be_1 C2_0Be_1 EfD_0Be_1 ED_0Be_1 run2_0Be_1 D2_0Be_1 W2_0Be_1 NX2_0Be_1 EQ2_0Be_1 RUN2_0Be_1 L2_0Be_1 AXD_0Be_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_0Be_1 TDr_0Be_1 CD_0Be Eps_0Be Ebg_0Be run3_0Be AXDr_0Be_1 ENTD_0Be_1 RUN3_0Be L3_0Be NX3_0Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 0%nat st true S1c_0Be_2 C2_0Be_2 EfD_0Be_2 ED_0Be_2 run2_0Be_2 D2_0Be_2 W2_0Be_2 NX2_0Be_2 EQ2_0Be_2 RUN2_0Be_2 L2_0Be_2 AXD_0Be_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_0Be_2 TDr_0Be_2 CD_0Be Eps_0Be Ebg_0Be run3_0Be AXDr_0Be_2 ENTD_0Be_2 RUN3_0Be L3_0Be NX3_0Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
End I0Be.
End F0A_i0Be.

