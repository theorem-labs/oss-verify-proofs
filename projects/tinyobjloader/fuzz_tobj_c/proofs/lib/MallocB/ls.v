(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_cN0 lo l0.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgEdgesA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_cN2.
From Stdlib Require Permutation FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lq F0A_cLN1.

(* [comment removed for export] *)
Module F0A_aN0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "AE_A"; "J_free_preT"; "Pre_freeI"; "Wcan"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "true"; "bool"; "pair"; "prod"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "junkF"; "j_min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_live"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "le"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_cN0"; "Erc_N0"; "ED_N0_1"; "ED_N0_2"; "TD_N0_1"; "TD_N0_2"; "P0_N0"; "PMID_N0"; "exits1_N0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "HDF"; "HDFE"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMax"; "SHADOW_BAND_HI"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "set_inited"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln"; "QFN"; "contN"; "econtN"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skeln F0A_cN0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.F0A_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_cN0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lo.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section AN0.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).

Lemma spine_tail_N0 : ltac2:(tb__ "0|2|
S0OF_;S1cOF_;S16S2S8S8SdScQ40M0A1A1S1dS3R5A1S25Vsegs;R8S23R6A1A3S2eR6R5A2S20S32SbG0S9R6PdA2A2A2S2fU0M1S1RcRbRaR9R7S27S29R5AaS2fG1S1RdRcRbRaR8S28S2aR6AaS3cG1ReRdRcRbR9S26R7A8S40S8S3eS40R2S2dA3S1fVsegs;R11S24Vsegs;S31G1S1SeR10RfRdA6R3R2RcA5RbA4F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HBIG E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  unfold exits1_N0 in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (f0_s2 0 UStopLe true S1c_N0_1 C2_N0_1 EfD_N0_1 ED_N0_1 run2_N0_1 D2_N0_1 W2_N0_1 NX2_N0_1 EQ2_N0_1 RUN2_N0_1 L2_N0_1 AXD_N0_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL.
    exact (f0_s3n 0 UStopLe TD_N0_1 TDr_N0_1 CD_N0 Eps_N0 Ebg_N0 Erc_N0 run3_N0 AXDr_N0_1 ENTD_N0_1 RUN3_N0 L3_N0 NX3_N0 SMF_N0 CertR_N0
             ok A' Kc rho rho1' tp' Q HUS HKc Hok (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
  - apply (f0_s2 0 UStopLe true S1c_N0_2 C2_N0_2 EfD_N0_2 ED_N0_2 run2_N0_2 D2_N0_2 W2_N0_2 NX2_N0_2 EQ2_N0_2 RUN2_N0_2 L2_N0_2 AXD_N0_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL.
    exact (f0_s3n 0 UStopLe TD_N0_2 TDr_N0_2 CD_N0 Eps_N0 Ebg_N0 Erc_N0 run3_N0 AXDr_N0_2 ENTD_N0_2 RUN3_N0 L3_N0 NX3_N0 SMF_N0 CertR_N0
             ok A' Kc rho rho1' tp' Q HUS HKc Hok (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
Qed.
Lemma espine_tail_N0 : ltac2:(tb__ "0|2|
S0OF_;S16S2S8S8SdScQ40M0A1A1S1cOF_;S3R5A1S2eR5R4A2S20S32SbG0S9R5PdA2A2A2S30U0M1S1RaR9R8R6S27S29R4A9S30G1S1RbRaR9R7S28S2aR5A9S3dG1RcRbRaR8S26R6A7S40S8S3eS40R2S2dA3S1eVsegs;S24Vsegs;S31G1S1SeRfReRcA6R3R2RbA5RaA3F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HBIG E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  unfold exits1_N0 in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (ef0_s2 0 UStopLe true S1c_N0_1 C2_N0_1 EfD_N0_1 ED_N0_1 run2_N0_1 D2_N0_1 W2_N0_1 NX2_N0_1 EQ2_N0_1 RUN2_N0_1 L2_N0_1 AXD_N0_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL.
    exact (ef0_s3n 0 UStopLe TD_N0_1 TDr_N0_1 CD_N0 Eps_N0 Ebg_N0 Erc_N0 run3_N0 AXDr_N0_1 ENTD_N0_1 RUN3_N0 L3_N0 NX3_N0 SMF_N0 NXB_N0 ECertR_N0
             A' Kc rho rho1' tp' Q HUS HKc (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
  - apply (ef0_s2 0 UStopLe true S1c_N0_2 C2_N0_2 EfD_N0_2 ED_N0_2 run2_N0_2 D2_N0_2 W2_N0_2 NX2_N0_2 EQ2_N0_2 RUN2_N0_2 L2_N0_2 AXD_N0_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL.
    exact (ef0_s3n 0 UStopLe TD_N0_2 TDr_N0_2 CD_N0 Eps_N0 Ebg_N0 Erc_N0 run3_N0 AXDr_N0_2 ENTD_N0_2 RUN3_N0 L3_N0 NX3_N0 SMF_N0 NXB_N0 ECertR_N0
             A' Kc rho rho1' tp' Q HUS HKc (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
Qed.

Theorem free_spine_N0 : ltac2:(tb__ "0|2|
S0OF_;S1cOF_;S16S2S8S8SdScQ40M0A1A1S1dS3R5A1S25Vsegs;R8S23R6A1A3S2eR6R5A2S20S32SbG0S9R6PdA2A2A2S2fU0M1S1RcRbRaR9R7S27S29R5AaS2fG1S1RdRcRbRaR8S28S2aR6AaS3cG1ReRdRcRbR9S26R7A8S8S1fVsegs;RfS24Vsegs;S31G1S1SeReRdRbA6S2bR1RaA5R9A4FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HBIG.
  apply (f0_s1c 0 UStopLe true P0_N0 exits1_N0 Cert1_N0 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_N0 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HBIG).
Qed.
Theorem efree_spine_N0 : ltac2:(tb__ "0|2|
S0OF_;S16S2S8S8SdScQ40M0A1A1S1cOF_;S3R5A1S2eR5R4A2S20S32SbG0S9R5PdA2A2A2S30U0M1S1RaR9R8R6S27S29R4A9S30G1S1RbRaR9R7S28S2aR5A9S3dG1RcRbRaR8S26R6A7S8S1eVsegs;S24Vsegs;S31G1S1SeRdRcRaA6S2bR1R9A5R8A3FrhoP;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HBIG.
  apply (ef0_s1c 0 UStopLe true P0_N0 exits1_N0 NX0_N0 ECert1_N0 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_N0 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HBIG).
Qed.

Theorem free_spine_m_N0 : ltac2:(tb__ "0|2|
S0OF_;S1cOF_;S16S2S8S8SdScQ40M0A1A1S1dS3R5A1S25Vsegs;R8S23R6A1A3S2eR6R5A2S20S32SbG0S9R6PdA2A2A2S2fU0M1S1RcRbRaR9R7S27S29R5AaS2fG1S1RdRcRbRaR8S28S2aR6AaS3cG1ReRdRcRbR9S26R7A8S8S1fVsegs;RfS24Vsegs;S31G1S1SeReRdRbA6S2cR1RaA5R9A4FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HBIG.
  apply (f0_s1c 0 UStopLe true PMID_N0 exits1_N0 Cert1m_N0 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_N0 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HBIG).
Qed.
Theorem efree_spine_m_N0 : ltac2:(tb__ "0|2|
S0OF_;S16S2S8S8SdScQ40M0A1A1S1cOF_;S3R5A1S2eR5R4A2S20S32SbG0S9R5PdA2A2A2S30U0M1S1RaR9R8R6S27S29R4A9S30G1S1RbRaR9R7S28S2aR5A9S3dG1RcRbRaR8S26R6A7S8S1eVsegs;S24Vsegs;S31G1S1SeRdRcRaA6S2cR1R9A5R8A3FrhoP;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HBIG.
  apply (ef0_s1c 0 UStopLe true PMID_N0 exits1_N0 NX0m_N0 ECert1m_N0 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_N0 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HBIG).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S0S44VCST;R1A2S1bS45R2A1A1F_;Fa;").

Theorem hdf_N0_1 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S3fS0S0S0S14S3R8A1S37SaRaR8R7R6A5S3eS11S0S0A2S10S0S0R6R5A4S18RbA1A3S42R7R6A2S19S0SbG0S9RbPcA2A2R8A3S36ReRcR9R8R7R6A6S1cOF_;S1dS25SaR2S23R10A1A3S41SaR3S23R11A1A3S2fU0S1S35VCST;VXGL;R13A3R4R13R12S13R13R11ReRdRcRbA6S27S29R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] ok Q Hok Hokp.
  exact (depot_call_HDFG 0 (rd_okG NVN 0) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_N0_1 TD_N0_1 (sD_of ED_N0_1 1) RD_N0_1 HeD_N0_1 HchkD_N0_1 HTD_N0_1 DCHK_N0_1
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 0) ok Q Hok Hokp).
Qed.
Theorem hdfe_N0_1 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S3fS0S0S0S14S3R8A1S37SaRaR8R7R6A5S3eS11S0S0A2S10S0S0R6R5A4S18RbA1A3S42R7R6A2S19S0SbG0S9RbPcA2A2R8A3S36ReRcR9R8R7R6A6S1cOF_;S30U0S1S35VCST;VXGL;R10A3R10RfS13R10ReRbRaR9R8A6S27S29R1A9FQ;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] Q.
  exact (depot_call_HDFEG 0 (rd_okG NVN 0) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_N0_1 TD_N0_1 (sD_of ED_N0_1 1) RD_N0_1 HeD_N0_1 HchkD_N0_1 HTD_N0_1 DCHK_N0_1
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 0) Q).
Qed.
Theorem hdf_N0_2 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S3fS0S0S0S14S3R8A1S37SaRaR8R7R6A5S3eS11S0S0A2S10S0S0R6R5A4S18RbA1A3S42R7R6A2S19S0SbG0S9RbPcA2A2R8A3S36ReRcR9R8R7R6A6S1cOF_;S1dS25SaR2S23R10A1A3S41SaR3S23R11A1A3S2fU0S1S35VCST;VXGL;R13A3R4R13R12S13R13R11ReRdRcRbA6S28S2aR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] ok Q Hok Hokp.
  exact (depot_call_HDFG 0 (rd_okG NVN 0) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_N0_2 TD_N0_2 (sD_of ED_N0_2 2) RD_N0_2 HeD_N0_2 HchkD_N0_2 HTD_N0_2 DCHK_N0_2
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 0) ok Q Hok Hokp).
Qed.
Theorem hdfe_N0_2 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S3fS0S0S0S14S3R8A1S37SaRaR8R7R6A5S3eS11S0S0A2S10S0S0R6R5A4S18RbA1A3S42R7R6A2S19S0SbG0S9RbPcA2A2R8A3S36ReRcR9R8R7R6A6S1cOF_;S30U0S1S35VCST;VXGL;R10A3R10RfS13R10ReRbRaR9R8A6S28S2aR1A9FQ;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] Q.
  exact (depot_call_HDFEG 0 (rd_okG NVN 0) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_N0_2 TD_N0_2 (sD_of ED_N0_2 2) RD_N0_2 HeD_N0_2 HchkD_N0_2 HTD_N0_2 DCHK_N0_2
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 0) Q).
Qed.

Theorem free_hi_N_0 : ltac2:(tb__ "0|3|
S1cOF_;S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S3bVCST;VXGL;U0M1R6R5R4R3A7S1dS3R6A1S25SaR9S23R7A1A3S41SaRaS23R8A1A3S21S33S22R6Z10A2A2S19SfS17RbA1SeA3S20S32R7A2S0S14S36RfRdRbRaR2R1A6S19S0S15R2A1S34A3S2eRfS13R11RfRdRcR4R3A6A2S3cG1S35VCST;VXGL;R12A3R13R12R11S13R12R10ReRdR5R4A6S26RcA8F_;F_;F_;Fjv;Ft;S1fSaRfS24SaS5S37SaA1S7G1A1M2S1ReRdA5S6S4G2S1A3RcRbA5R8A4F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii HBG HBIG. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (entry_pureN true (Wcan 0) UStopLe A rho)); [intros w Hw; exact (entry_pure_N true _ _ A Kc rho tp w HHI Hii HBG Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros k Hg w Hw.
  destruct (g_instantiate true 0 UStopLe NVN VFN Wa_N0 Da_N0 Wb_N0 Wc_N0 Wd_N0 Fb_N0 XI_N0 A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree A rho p n t jv) IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A rho p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl); exact HBG).
  exact (free_spine_N0 (KEEPD CST XGL A) ok A Kc rho (rhoF_of A rho p n t jv) tp Q HKc Hok HR Hn1
           (hdf_N0_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ ok _ Hok Hokp) (hdf_N0_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ ok _ Hok Hokp)
           (HBIG t jv HTJ HJM HR) (rhoF_of A rho p n t jv) k Hg w Hw1).
Qed.
Theorem efree_hi_N_0 : ltac2:(tb__ "0|3|
S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S3bVCST;VXGL;U0M1R6R5R4R3A7S1dS3R6A1S21S33S22R4Z10A2A2S19SfS17R9A1SeA3S20S32R5A2S0S14S36RdRbR9R8R2R1A6S19S0S15R2A1S34A3S2eRdS13RfRdRbRaR4R3A6A2S3dG1S35VCST;VXGL;R10A3R10RfS13R10ReRcRbR5R4A6S26RaA7F_;F_;F_;Fjv;Ft;S1eSaS24SaS5S37SaA1S7G1A1M2S1RcRbA5S6S4G2S1A3RaR9A5R6A3F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii HBG HBIG. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (entry_pureN true (Wcan 0) UStopLe A rho)); [intros w Hw; exact (entry_pure_N true _ _ A Kc rho tp w HHI Hii HBG Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros w Hw.
  destruct (g_instantiate true 0 UStopLe NVN VFN Wa_N0 Da_N0 Wb_N0 Wc_N0 Wd_N0 Fb_N0 XI_N0 A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree A rho p n t jv) IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A rho p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl); exact HBG).
  exact (efree_spine_N0 (KEEPD CST XGL A) A Kc rho (rhoF_of A rho p n t jv) tp Q HKc HR Hn1
           (hdfe_N0_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ _) (hdfe_N0_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ _)
           (HBIG t jv HTJ HJM HR) (rhoF_of A rho p n t jv) w Hw1).
Qed.

Hypothesis HCST2 : ltac2:(tb__ "0|0|
S0S44VCST;R1A2S1aS1bS1aS21S39R2A2S20R2S3aA2A2A1S1bS1aS21Z17db48R2A2S20R2Z17db4cA2A2A1A2F_;Fa;").
Theorem free_hi_ia0_N_0 : ltac2:(tb__ "0|4|
S1cOF_;S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S3bVCST;VXGL;U0M1R6R5R4R3A7S1dS3R6A1S25SaR9S23R7A1A3S41SaRaS23R8A1A3S21S33S22R6Z10A2A2S19SfS17RbA1S12A3S20S32R7A2S8S0S14S43R10S13R10ReRcRbR2R1A6R3A3S36S38R11A1R4RdRcR3R2A6S19S0S15R3A1S34A3S2eR6S13S38R13A1R6RfReR5R4A6A2S3cG1S35VCST;VXGL;S38R14A1M2A3R15G2R13S13G2R7R10RfR6R5A6S26S3bVCST;VXGL;G1G2R13R7R11A7A8F_;F_;F_;F_;Fjv;Ft;Frho2;S1fSaRfS24SaS5S37SaA1S7G1A1M3S1ReRdA5S6S4G3S1A3RcRbA5R8A4F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii HBG HBIG. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix 0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Wai_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Dai_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Wbi_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Wci_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Certi_0A ok A Kc rho tp Q p n t jv Hii HKc Hok).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 0 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (triple_pre_pure segsA ok _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instG_facts true (Wcan 0) UStopLe NVN VFN (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_N A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true (Wcan 0) UStopLe HHI HBG). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (g_instantiate_mid true 0 UStopLe NVN VFN Wbm_N0 Wcm_N0 Wdm_N0 Fb_N0 XIm_N0 A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A1 rho2 p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl), E13; exact HBG).
  exact (free_spine_m_N0 (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR Hn1
           (hdf_N0_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ ok _ Hok Hokp) (hdf_N0_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR) (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.
Theorem efree_hi_ia0_N_0 : ltac2:(tb__ "0|4|
S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S3bVCST;VXGL;U0M1R6R5R4R3A7S1dS3R6A1S21S33S22R4Z10A2A2S19SfS17R9A1S12A3S20S32R5A2S8S0S14S43ReS13ReRcRaR9R2R1A6R3A3S36S38RfA1R4RbRaR3R2A6S19S0S15R3A1S34A3S2eR6S13S38R11A1R6RdRcR5R4A6A2S3dG1S35VCST;VXGL;S38R12A1M2A3G2R11S13G2R7ReRdR6R5A6S26S3bVCST;VXGL;G1G2R11R7RfA7A7F_;F_;F_;F_;Fjv;Ft;Frho2;S1eSaS24SaS5S37SaA1S7G1A1M3S1RcRbA5S6S4G3S1A3RaR9A5R6A3F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii HBG HBIG. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix 0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Wai_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Dai_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Wbi_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Wci_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.ECerti_0A A Kc rho tp Q p n t jv Hii HKc).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 0 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (etriple_pre_pure segsA _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instG_facts true (Wcan 0) UStopLe NVN VFN (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_N A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true (Wcan 0) UStopLe HHI HBG). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (g_instantiate_mid true 0 UStopLe NVN VFN Wbm_N0 Wcm_N0 Wdm_N0 Fb_N0 XIm_N0 A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A1 rho2 p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl), E13; exact HBG).
  exact (efree_spine_m_N0 (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR Hn1
           (hdfe_N0_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ _) (hdfe_N0_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ _)
           (HBIG rho2 t jv ML HTJ JM HR) (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End AN0.
End F0A_aN0.

(* [comment removed for export] *)
Module MallocHit2.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "sv"; "SVar"; "rw"; "sprop_below"; "swf"; "SLit"; "@Corelib.Init.Logic"; "eq"; "not"; "False"; "@Corelib.Init.Datatypes"; "app"; "bool"; "list"; "true"; "prod"; "nil"; "pair"; "cons"; "Some"; "fst"; "option"; "orb"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "AE_A"; "Wcan"; "Pre_mallocI"; "KcA"; "Kc_ok"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "JL_malloc_ok"; "J_alloc_preT"; "L_malloc_ok"; "Posts_malloc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.Lists.List"; "forallb"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "F_geom_fn"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "E_s1"; "F_s1"; "F_hi"; "F_lo"; "s1_cuts"; "s1_exits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "E3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "MAP1"; "MAP1N"; "STORE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cnt_of"; "sa_m"; "sb_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@Stdlib.ZArith.BinInt.Z"; "add"; "leb"; "mul"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ls.MallocHit2"; "cstD_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ji.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i9.CertMallocSPc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i9.CertMallocSPd OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineMallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineMallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j7.SpineMallocS5iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.SpineMallocS6iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.SpineMallocS7iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineMallocS8iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineMallocS9iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ji.SpineMallocS9jW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l3.DepotCallHW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3c OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineMallocS5t OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l0.MallocHitTail2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SpineMallocS12iW2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgEdgesA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma Wa_0 : ltac2:(tb__ "0|0|
S9SdS7S44S1bU2A1S19A2A1SfA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Da_0 : ltac2:(tb__ "0|5|
S9S16S10SeS10S3S3A2M0A1M1SeS1A1M2A2M3A1S4cS31S1cS1aS1bU2A1M4S19A3A1S44G4S19A2A2S14G3S12G1G2S13G0S12S3S3S4P18A1S8S50A1A4S11G0A1A3S11S1A1A4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Wb_0 : ltac2:(tb__ "0|0|
S9SdS7S45S1bU2A1S19A2A1SfA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Fbh_0 : ltac2:(tb__ "0|0|
S9SdS2dS1S6S36A1ScS1ScS1ScS1ScS1S21S1bU2A1S19A2S20S1fA1A3S35A3S38A3S39A3A3SfA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Fbl_0 : ltac2:(tb__ "0|0|
S9SdS2dS1S6S36A1ScS1ScS1ScS1ScS1S21S1bU2A1S19A2S20S1fA1A3S35A3S38A3S3aA3A3SfA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma Cert1_0 : ltac2:(tb__ "0|1|
S9SdS4dS4fUfa0S13S0Z40bacS11S0A1A3S4eS3bU2M0S19A2S3cG0S19Z4A3A6SfA3"). Proof. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgEdgesA.check_cfgA_of_ecfgA segsA 4000%nat [0x40bac] GW (map (fun c => mkVNA c 1 (SLit 0)) (s1_cuts 2 UStopLe)) (map (fun e => mkVNA e 0 (SLit 0)) (s1_exits 2 UStopLe 4)) (s1_cuts 2 UStopLe) (s1_exits 2 UStopLe 4) eq_refl eq_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.SpineMallocEiW2.ECert1_0). Qed.

Definition cstD_okb (CST : list (Z * Z)) : bool := ltac2:(tb__ "0|2|
S2dS10S0S0A2M0G0S17S48S47S15S0S0R1A3M1S18S0S0R1A3A2S42A2S48S47S40S49Z8S41A2A2G1A2A2Lr;VCST;A3").
Lemma cstD_okb_sound : ltac2:(tb__ "0|0|
SeS10S0S0A2A1S9SdS51R1A1SfA3S0S2cR3R1A2SaS3fR2A1A1F_;Fa;F_;FCST;").
Proof.
  intros CST H a (b & n & Hin & Ha) Hs. pose proof (proj1 (forallb_forall _ _) H (b, n) Hin) as X. cbn [fst snd] in X.
  pose proof (dstat_range a Hs) as R. apply orb_prop in X as [X|X]; apply Z.leb_le in X; lia.
Qed.

Section HIT0.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S0S2cVCST;R1A2S2cS52R2A2SbF_;F_;Fa;").

Hypothesis HCSTD : ltac2:(tb__ "0|0|
S0S2cVCST;R1A2SaS3fR2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S23VAInv;VW;Vst;VA;VKc;S4PcA1A6").

Let law_die : forall A rho tp md, AInv A rho tp md -> cell_ok (view segs (rm rho)) (mkACell 0x17fbdc 4 0) := AInvA_die.
Let law_inv3 : forall A rho tp md, AInv A rho tp md -> inv3 A := AInvA_inv3.
Let W0 : list ulink := Wcan 2.
Let st0 : ustop := UStopLe.

Theorem malloc_hit_2_P : ltac2:(tb__ "0|4|
S28OF_;S3eS1dS2SeS4aQ40M0A1A1SeS10S30S33A2M1A1S32Vsegs;S2fR3R2R1A5S27S2eG1S12S30S33S24S1aVW0;Vst0;A3S22VAInv;VCST;VXGL;R6R5A5A4R2A3S1eR6A1S2bVsegs;R9S2aR7A1A3S34Vsegs;RaS2aR8A1A3S9S0S43RaS4bG0S5R8PcA2A2A2Z0A3S2S26Vsegs;RdS29Vsegs;S46VW0;Vst0;RcRbRaA5M2S3dVW0;Vst0;Z4M3A3R1R9A5R7A4FrhoE;F_;S2S26Vsegs;RdS29Vsegs;G2S37VW0;Vst0;G3Z8A4R1R9A5R7A4FrhoE;S26Vsegs;RdS29Vsegs;VJ;VW0;Vst0;RcRbA4S1cS1aVW0;Vst0;A3RaR9A5R7A4F_;F_;F_;F_;F_;F_;TQ;FPosts;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Posts Q HPin HKc Hokl Hokpl HREF HSEC.
  assert (Hokf : forall A', ok_frameA segs ok (J W0 st0 A' Kc)).
  { intros A' r t tr ms md msv' HJ. apply (Hokl r t tr ms md msv'). destruct HJ as (_ & HK & _). exact HK. }
  assert (HUS : stopJ_stable W0 st0) by (apply stopJ_stable_le).
  assert (HW : st0 = UStopLeOrPc -> W0 = []) by (intros E; discriminate E).

  apply (spine_s1 law_die 2%nat st0 4 WC1_2 DC1_2 Cert1_0 ok A Kc rho tp Q HW HUS HKc (Hokf A) Wa_0 Da_0 Wb_0 Fbh_0 Fbl_0); [|exact HSEC].
  intros rhoE1.

  apply (spine_s2c 2%nat st0 4 Cert2_0 OVa_2 OVb_2 TABa_2 TABb_2 Wa'_2 Wb'_0 Da'_2 Db'_0 NXa_2 NXb_0 Fa_0 Fb_0 Ga_0 Gb_0 SKa_0 SKb_0 XXa_0 XXb_0 XFa_0 XFb_0
           W1a_0 W1ba_0 W1ca_0 W2a_0 W1ra_0 W2ra_0 W1b_0 W1bb_0 W1cb_0 W2b_0 W1rb_0 W2rb_0 sa_0 sra_0 sb_0 srb_0 ENTa_0 ENTra_0 ENTb_0 ENTrb_0
           SIDa_0 SIDra_0 SIDb_0 SIDrb_0 FB_0 FBr_0 ok A Kc rho tp Q HW HUS HKc (Hokf A)).
  2: { intros Hz0 rhoE2. apply (spine_s3r 2%nat st0 4 Cert3r_0 ok A Kc rho tp Q HUS HKc (Hokf A)). exact (HREF Hz0). }
  intros rhoE2.

  apply (spine_s3p_cert 2%nat st0 4 Cert3p_0 ok A Kc rho tp Q HUS HKc (Hokf A)).
  exact (malloc_hit_tail_2_P CST XGL HCST HXGL HCSTM HCSTD ok A Kc rho tp Posts HPin HKc Hokl Hokpl).
Qed.

Theorem malloc_hit_2 : ltac2:(tb__ "0|3|
S28OF_;S3eS1dS2SeS4aQ40M0A1A1S32Vsegs;S2fR2R1S25S1aVAInv;VCST;VXGL;VW0;Vst0;R4R3A8A5S27S1eR4A1S2bVsegs;R7S2aR5A1A3S34Vsegs;R8S2aR6A1A3S9S0S43R8S4bG0S5R6PcA2A2A2Z0A3S2S26Vsegs;RbS29Vsegs;S46VW0;Vst0;RaR9R8A5M1S3dVW0;Vst0;Z4M2A3R1R7A5R6A4FrhoE;F_;S2S26Vsegs;RbS29Vsegs;G1S37VW0;Vst0;G2Z8A4R1R7A5R6A4FrhoE;S26Vsegs;RbS29Vsegs;VJ;VW0;Vst0;RaR9A4S1cS1aVW0;Vst0;A3R8R7A5R6A4F_;F_;F_;F_;F_;TQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp. exact (malloc_hit_2_P ok A Kc rho tp (Posts_malloc AE_A AInv CST XGL W0 st0 A Kc) (or_intror (or_introl eq_refl))).
Qed.
End HIT0.
End MallocHit2.

(* [comment removed for export] *)
Module F0A_aN2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "AE_A"; "J_free_preT"; "Pre_freeI"; "Wcan"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "true"; "bool"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "junkF"; "j_min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "aa_internal_inited"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "rigF"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "set_inited"; "IA_BEG"; "IA_END"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "le"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_cN2"; "Erc_N2"; "ED_N2_1"; "ED_N2_2"; "ED_N2_3"; "ED_N2_4"; "TD_N2_1"; "TD_N2_2"; "TD_N2_3"; "TD_N2_4"; "P0_N2"; "PMID_N2"; "exits1_N2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMax"; "SHADOW_BAND_HI"; "kQuarantineMin"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln"; "QFN"; "contN"; "econtN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skeln F0A_cN2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.F0A_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_cN2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lo.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section AN2.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).

Lemma spine_tail_N2 : ltac2:(tb__ "0|2|
S0OF_;S1cOF_;S16S2S8S8SdScQ40M0A1A1S1dS3R5A1S26Vsegs;R8S24R6A1A3S22R6R5A2S2dS3cSbG0S9R6PdA2A2A2S20U2M1S1RcRbRaR9R7S31S35R5AaS20G1S1RdRcRbRaR8S32S36R6AaS20G1S1ReRdRcRbR9S33S37R7AaS20G1S1RfReRdRcRaS34S38R8AaS44G1R10RfReRdRbS30R9A8S46S8S3fS46R2S3bA3S1fVsegs;R13S25Vsegs;S23G1S1S10R12R11RfA6R3R2ReA5RdA4F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HD4 HBIG E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 2) UStopLe) by apply stopJ_stable_le.
  unfold exits1_N2 in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (f0_s2 2 UStopLe true S1c_N2_1 C2_N2_1 EfD_N2_1 ED_N2_1 run2_N2_1 D2_N2_1 W2_N2_1 NX2_N2_1 EQ2_N2_1 RUN2_N2_1 L2_N2_1 AXD_N2_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL.
    exact (f0_s3n 2 UStopLe TD_N2_1 TDr_N2_1 CD_N2 Eps_N2 Ebg_N2 Erc_N2 run3_N2 AXDr_N2_1 ENTD_N2_1 RUN3_N2 L3_N2 NX3_N2 SMF_N2 CertR_N2
             ok A' Kc rho rho1' tp' Q HUS HKc Hok (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
  - apply (f0_s2 2 UStopLe true S1c_N2_2 C2_N2_2 EfD_N2_2 ED_N2_2 run2_N2_2 D2_N2_2 W2_N2_2 NX2_N2_2 EQ2_N2_2 RUN2_N2_2 L2_N2_2 AXD_N2_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL.
    exact (f0_s3n 2 UStopLe TD_N2_2 TDr_N2_2 CD_N2 Eps_N2 Ebg_N2 Erc_N2 run3_N2 AXDr_N2_2 ENTD_N2_2 RUN3_N2 L3_N2 NX3_N2 SMF_N2 CertR_N2
             ok A' Kc rho rho1' tp' Q HUS HKc Hok (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
  - apply (f0_s2 2 UStopLe true S1c_N2_3 C2_N2_3 EfD_N2_3 ED_N2_3 run2_N2_3 D2_N2_3 W2_N2_3 NX2_N2_3 EQ2_N2_3 RUN2_N2_3 L2_N2_3 AXD_N2_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL.
    exact (f0_s3n 2 UStopLe TD_N2_3 TDr_N2_3 CD_N2 Eps_N2 Ebg_N2 Erc_N2 run3_N2 AXDr_N2_3 ENTD_N2_3 RUN3_N2 L3_N2 NX3_N2 SMF_N2 CertR_N2
             ok A' Kc rho rho1' tp' Q HUS HKc Hok (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
  - apply (f0_s2 2 UStopLe true S1c_N2_4 C2_N2_4 EfD_N2_4 ED_N2_4 run2_N2_4 D2_N2_4 W2_N2_4 NX2_N2_4 EQ2_N2_4 RUN2_N2_4 L2_N2_4 AXD_N2_4
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL.
    exact (f0_s3n 2 UStopLe TD_N2_4 TDr_N2_4 CD_N2 Eps_N2 Ebg_N2 Erc_N2 run3_N2 AXDr_N2_4 ENTD_N2_4 RUN3_N2 L3_N2 NX3_N2 SMF_N2 CertR_N2
             ok A' Kc rho rho1' tp' Q HUS HKc Hok (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
Qed.
Lemma espine_tail_N2 : ltac2:(tb__ "0|2|
S0OF_;S16S2S8S8SdScQ40M0A1A1S1cOF_;S3R5A1S22R5R4A2S2dS3cSbG0S9R5PdA2A2A2S21U2M1S1RaR9R8R6S31S35R4A9S21G1S1RbRaR9R7S32S36R5A9S21G1S1RcRbRaR8S33S37R6A9S21G1S1RdRcRbR9S34S38R7A9S45G1ReRdRcRaS30R8A7S46S8S3fS46R2S3bA3S1eVsegs;S25Vsegs;S23G1S1S10R11R10ReA6R3R2RdA5RcA3F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HD4 HBIG E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 2) UStopLe) by apply stopJ_stable_le.
  unfold exits1_N2 in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (ef0_s2 2 UStopLe true S1c_N2_1 C2_N2_1 EfD_N2_1 ED_N2_1 run2_N2_1 D2_N2_1 W2_N2_1 NX2_N2_1 EQ2_N2_1 RUN2_N2_1 L2_N2_1 AXD_N2_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL.
    exact (ef0_s3n 2 UStopLe TD_N2_1 TDr_N2_1 CD_N2 Eps_N2 Ebg_N2 Erc_N2 run3_N2 AXDr_N2_1 ENTD_N2_1 RUN3_N2 L3_N2 NX3_N2 SMF_N2 NXB_N2 ECertR_N2
             A' Kc rho rho1' tp' Q HUS HKc (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
  - apply (ef0_s2 2 UStopLe true S1c_N2_2 C2_N2_2 EfD_N2_2 ED_N2_2 run2_N2_2 D2_N2_2 W2_N2_2 NX2_N2_2 EQ2_N2_2 RUN2_N2_2 L2_N2_2 AXD_N2_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL.
    exact (ef0_s3n 2 UStopLe TD_N2_2 TDr_N2_2 CD_N2 Eps_N2 Ebg_N2 Erc_N2 run3_N2 AXDr_N2_2 ENTD_N2_2 RUN3_N2 L3_N2 NX3_N2 SMF_N2 NXB_N2 ECertR_N2
             A' Kc rho rho1' tp' Q HUS HKc (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
  - apply (ef0_s2 2 UStopLe true S1c_N2_3 C2_N2_3 EfD_N2_3 ED_N2_3 run2_N2_3 D2_N2_3 W2_N2_3 NX2_N2_3 EQ2_N2_3 RUN2_N2_3 L2_N2_3 AXD_N2_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL.
    exact (ef0_s3n 2 UStopLe TD_N2_3 TDr_N2_3 CD_N2 Eps_N2 Ebg_N2 Erc_N2 run3_N2 AXDr_N2_3 ENTD_N2_3 RUN3_N2 L3_N2 NX3_N2 SMF_N2 NXB_N2 ECertR_N2
             A' Kc rho rho1' tp' Q HUS HKc (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
  - apply (ef0_s2 2 UStopLe true S1c_N2_4 C2_N2_4 EfD_N2_4 ED_N2_4 run2_N2_4 D2_N2_4 W2_N2_4 NX2_N2_4 EQ2_N2_4 RUN2_N2_4 L2_N2_4 AXD_N2_4
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL.
    exact (ef0_s3n 2 UStopLe TD_N2_4 TDr_N2_4 CD_N2 Eps_N2 Ebg_N2 Erc_N2 run3_N2 AXDr_N2_4 ENTD_N2_4 RUN3_N2 L3_N2 NX3_N2 SMF_N2 NXB_N2 ECertR_N2
             A' Kc rho rho1' tp' Q HUS HKc (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
Qed.

Theorem free_spine_N2 : ltac2:(tb__ "0|2|
S0OF_;S1cOF_;S16S2S8S8SdScQ40M0A1A1S1dS3R5A1S26Vsegs;R8S24R6A1A3S22R6R5A2S2dS3cSbG0S9R6PdA2A2A2S20U2M1S1RcRbRaR9R7S31S35R5AaS20G1S1RdRcRbRaR8S32S36R6AaS20G1S1ReRdRcRbR9S33S37R7AaS20G1S1RfReRdRcRaS34S38R8AaS44G1R10RfReRdRbS30R9A8S8S1fVsegs;R11S25Vsegs;S23G1S1S10R10RfRdA6S39R1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HD4 HBIG.
  apply (f0_s1c 2 UStopLe true P0_N2 exits1_N2 Cert1_N2 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_N2 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HD4 HBIG).
Qed.
Theorem efree_spine_N2 : ltac2:(tb__ "0|2|
S0OF_;S16S2S8S8SdScQ40M0A1A1S1cOF_;S3R5A1S22R5R4A2S2dS3cSbG0S9R5PdA2A2A2S21U2M1S1RaR9R8R6S31S35R4A9S21G1S1RbRaR9R7S32S36R5A9S21G1S1RcRbRaR8S33S37R6A9S21G1S1RdRcRbR9S34S38R7A9S45G1ReRdRcRaS30R8A7S8S1eVsegs;S25Vsegs;S23G1S1S10RfReRcA6S39R1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HD4 HBIG.
  apply (ef0_s1c 2 UStopLe true P0_N2 exits1_N2 NX0_N2 ECert1_N2 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_N2 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HD4 HBIG).
Qed.

Theorem free_spine_m_N2 : ltac2:(tb__ "0|2|
S0OF_;S1cOF_;S16S2S8S8SdScQ40M0A1A1S1dS3R5A1S26Vsegs;R8S24R6A1A3S22R6R5A2S2dS3cSbG0S9R6PdA2A2A2S20U2M1S1RcRbRaR9R7S31S35R5AaS20G1S1RdRcRbRaR8S32S36R6AaS20G1S1ReRdRcRbR9S33S37R7AaS20G1S1RfReRdRcRaS34S38R8AaS44G1R10RfReRdRbS30R9A8S8S1fVsegs;R11S25Vsegs;S23G1S1S10R10RfRdA6S3aR1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HD4 HBIG.
  apply (f0_s1c 2 UStopLe true PMID_N2 exits1_N2 Cert1m_N2 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_N2 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HD4 HBIG).
Qed.
Theorem efree_spine_m_N2 : ltac2:(tb__ "0|2|
S0OF_;S16S2S8S8SdScQ40M0A1A1S1cOF_;S3R5A1S22R5R4A2S2dS3cSbG0S9R5PdA2A2A2S21U2M1S1RaR9R8R6S31S35R4A9S21G1S1RbRaR9R7S32S36R5A9S21G1S1RcRbRaR8S33S37R6A9S21G1S1RdRcRbR9S34S38R7A9S45G1ReRdRcRaS30R8A7S8S1eVsegs;S25Vsegs;S23G1S1S10RfReRcA6S3aR1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HD4 HBIG.
  apply (ef0_s1c 2 UStopLe true PMID_N2 exits1_N2 NX0m_N2 ECert1m_N2 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_N2 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HD4 HBIG).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S0S48VCST;R1A2S1bS49R2A1A1F_;Fa;").

Theorem hdf_N2_1 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S40S0S0S0S14S3R8A1S29SaRaR8R7R6A5S3fSfS0S0A2SeS0S0R6R5A4S17RbA1A3S41R7R6A2S19S0SbG0S9RbPcA2A2R8A3S28ReRcR9R8R7R6A6S1cOF_;S1dS26SaR2S24R10A1A3S42SaR3S24R11A1A3S20U2S1S27VCST;VXGL;R13A3R4R13R12S13R13R11ReRdRcRbA6S31S35R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] ok Q Hok Hokp.
  exact (depot_call_HDFG 2 (rd_okG NVN 2) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_N2_1 TD_N2_1 (sD_of ED_N2_1 1) RD_N2_1 HeD_N2_1 HchkD_N2_1 HTD_N2_1 DCHK_N2_1
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 2) ok Q Hok Hokp).
Qed.
Theorem hdfe_N2_1 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S40S0S0S0S14S3R8A1S29SaRaR8R7R6A5S3fSfS0S0A2SeS0S0R6R5A4S17RbA1A3S41R7R6A2S19S0SbG0S9RbPcA2A2R8A3S28ReRcR9R8R7R6A6S1cOF_;S21U2S1S27VCST;VXGL;R10A3R10RfS13R10ReRbRaR9R8A6S31S35R1A9FQ;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] Q.
  exact (depot_call_HDFEG 2 (rd_okG NVN 2) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_N2_1 TD_N2_1 (sD_of ED_N2_1 1) RD_N2_1 HeD_N2_1 HchkD_N2_1 HTD_N2_1 DCHK_N2_1
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 2) Q).
Qed.
Theorem hdf_N2_2 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S40S0S0S0S14S3R8A1S29SaRaR8R7R6A5S3fSfS0S0A2SeS0S0R6R5A4S17RbA1A3S41R7R6A2S19S0SbG0S9RbPcA2A2R8A3S28ReRcR9R8R7R6A6S1cOF_;S1dS26SaR2S24R10A1A3S42SaR3S24R11A1A3S20U2S1S27VCST;VXGL;R13A3R4R13R12S13R13R11ReRdRcRbA6S32S36R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] ok Q Hok Hokp.
  exact (depot_call_HDFG 2 (rd_okG NVN 2) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_N2_2 TD_N2_2 (sD_of ED_N2_2 2) RD_N2_2 HeD_N2_2 HchkD_N2_2 HTD_N2_2 DCHK_N2_2
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 2) ok Q Hok Hokp).
Qed.
Theorem hdfe_N2_2 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S40S0S0S0S14S3R8A1S29SaRaR8R7R6A5S3fSfS0S0A2SeS0S0R6R5A4S17RbA1A3S41R7R6A2S19S0SbG0S9RbPcA2A2R8A3S28ReRcR9R8R7R6A6S1cOF_;S21U2S1S27VCST;VXGL;R10A3R10RfS13R10ReRbRaR9R8A6S32S36R1A9FQ;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] Q.
  exact (depot_call_HDFEG 2 (rd_okG NVN 2) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_N2_2 TD_N2_2 (sD_of ED_N2_2 2) RD_N2_2 HeD_N2_2 HchkD_N2_2 HTD_N2_2 DCHK_N2_2
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 2) Q).
Qed.
Theorem hdf_N2_3 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S40S0S0S0S14S3R8A1S29SaRaR8R7R6A5S3fSfS0S0A2SeS0S0R6R5A4S17RbA1A3S41R7R6A2S19S0SbG0S9RbPcA2A2R8A3S28ReRcR9R8R7R6A6S1cOF_;S1dS26SaR2S24R10A1A3S42SaR3S24R11A1A3S20U2S1S27VCST;VXGL;R13A3R4R13R12S13R13R11ReRdRcRbA6S33S37R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] ok Q Hok Hokp.
  exact (depot_call_HDFG 2 (rd_okG NVN 2) 3 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_N2_3 TD_N2_3 (sD_of ED_N2_3 3) RD_N2_3 HeD_N2_3 HchkD_N2_3 HTD_N2_3 DCHK_N2_3
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 2) ok Q Hok Hokp).
Qed.
Theorem hdfe_N2_3 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S40S0S0S0S14S3R8A1S29SaRaR8R7R6A5S3fSfS0S0A2SeS0S0R6R5A4S17RbA1A3S41R7R6A2S19S0SbG0S9RbPcA2A2R8A3S28ReRcR9R8R7R6A6S1cOF_;S21U2S1S27VCST;VXGL;R10A3R10RfS13R10ReRbRaR9R8A6S33S37R1A9FQ;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] Q.
  exact (depot_call_HDFEG 2 (rd_okG NVN 2) 3 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_N2_3 TD_N2_3 (sD_of ED_N2_3 3) RD_N2_3 HeD_N2_3 HchkD_N2_3 HTD_N2_3 DCHK_N2_3
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 2) Q).
Qed.
Theorem hdf_N2_4 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S40S0S0S0S14S3R8A1S29SaRaR8R7R6A5S3fSfS0S0A2SeS0S0R6R5A4S17RbA1A3S41R7R6A2S19S0SbG0S9RbPcA2A2R8A3S28ReRcR9R8R7R6A6S1cOF_;S1dS26SaR2S24R10A1A3S42SaR3S24R11A1A3S20U2S1S27VCST;VXGL;R13A3R4R13R12S13R13R11ReRdRcRbA6S34S38R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] ok Q Hok Hokp.
  exact (depot_call_HDFG 2 (rd_okG NVN 2) 4 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_N2_4 TD_N2_4 (sD_of ED_N2_4 4) RD_N2_4 HeD_N2_4 HchkD_N2_4 HTD_N2_4 DCHK_N2_4
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 2) ok Q Hok Hokp).
Qed.
Theorem hdfe_N2_4 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S40S0S0S0S14S3R8A1S29SaRaR8R7R6A5S3fSfS0S0A2SeS0S0R6R5A4S17RbA1A3S41R7R6A2S19S0SbG0S9RbPcA2A2R8A3S28ReRcR9R8R7R6A6S1cOF_;S21U2S1S27VCST;VXGL;R10A3R10RfS13R10ReRbRaR9R8A6S34S38R1A9FQ;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] Q.
  exact (depot_call_HDFEG 2 (rd_okG NVN 2) 4 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_N2_4 TD_N2_4 (sD_of ED_N2_4 4) RD_N2_4 HeD_N2_4 HchkD_N2_4 HTD_N2_4 DCHK_N2_4
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 2) Q).
Qed.

Theorem free_hi_N_2 : ltac2:(tb__ "0|3|
S1cOF_;S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S43VCST;VXGL;U2M1R6R5R4R3A7S1dS3R6A1S26SaR9S24R7A1A3S42SaRaS24R8A1A3S2eS3dS2fR6Z10A2A2S19S11S18RbA1S10A3S2dS3cR7A2S0S14S28RfRdRbRaR2R1A6S19S0S15R2A1S3eA3S22RfS13R11RfRdRcR4R3A6A2S44G1S27VCST;VXGL;R12A3R13R12R11S13R12R10ReRdR5R4A6S30RcA8F_;F_;F_;Fjv;Ft;S1fSaRfS25SaS5S29SaA1S7G1A1M2S1ReRdA5S6S4G2S1A3RcRbA5R8A4F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii HBG HBIG. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (entry_pureN true (Wcan 2) UStopLe A rho)); [intros w Hw; exact (entry_pure_N true _ _ A Kc rho tp w HHI Hii HBG Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros k Hg w Hw.
  destruct (g_instantiate true 2 UStopLe NVN VFN Wa_N2 Da_N2 Wb_N2 Wc_N2 Wd_N2 Fb_N2 XI_N2 A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree A rho p n t jv) IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A rho p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl); exact HBG).
  exact (free_spine_N2 (KEEPD CST XGL A) ok A Kc rho (rhoF_of A rho p n t jv) tp Q HKc Hok HR Hn1
           (hdf_N2_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ ok _ Hok Hokp) (hdf_N2_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ ok _ Hok Hokp) (hdf_N2_3 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ ok _ Hok Hokp) (hdf_N2_4 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ ok _ Hok Hokp)
           (HBIG t jv HTJ HJM HR) (rhoF_of A rho p n t jv) k Hg w Hw1).
Qed.
Theorem efree_hi_N_2 : ltac2:(tb__ "0|3|
S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S43VCST;VXGL;U2M1R6R5R4R3A7S1dS3R6A1S2eS3dS2fR4Z10A2A2S19S11S18R9A1S10A3S2dS3cR5A2S0S14S28RdRbR9R8R2R1A6S19S0S15R2A1S3eA3S22RdS13RfRdRbRaR4R3A6A2S45G1S27VCST;VXGL;R10A3R10RfS13R10ReRcRbR5R4A6S30RaA7F_;F_;F_;Fjv;Ft;S1eSaS25SaS5S29SaA1S7G1A1M2S1RcRbA5S6S4G2S1A3RaR9A5R6A3F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii HBG HBIG. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (entry_pureN true (Wcan 2) UStopLe A rho)); [intros w Hw; exact (entry_pure_N true _ _ A Kc rho tp w HHI Hii HBG Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros w Hw.
  destruct (g_instantiate true 2 UStopLe NVN VFN Wa_N2 Da_N2 Wb_N2 Wc_N2 Wd_N2 Fb_N2 XI_N2 A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree A rho p n t jv) IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A rho p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl); exact HBG).
  exact (efree_spine_N2 (KEEPD CST XGL A) A Kc rho (rhoF_of A rho p n t jv) tp Q HKc HR Hn1
           (hdfe_N2_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ _) (hdfe_N2_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ _) (hdfe_N2_3 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ _) (hdfe_N2_4 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ _)
           (HBIG t jv HTJ HJM HR) (rhoF_of A rho p n t jv) w Hw1).
Qed.

Hypothesis HCST2 : ltac2:(tb__ "0|0|
S0S48VCST;R1A2S1aS1bS1aS2eS2bR2A2S2dR2S2cA2A2A1S1bS1aS2eZ17db48R2A2S2dR2Z17db4cA2A2A1A2F_;Fa;").
Theorem free_hi_ia0_N_2 : ltac2:(tb__ "0|4|
S1cOF_;S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S43VCST;VXGL;U2M1R6R5R4R3A7S1dS3R6A1S26SaR9S24R7A1A3S42SaRaS24R8A1A3S2eS3dS2fR6Z10A2A2S19S11S18RbA1S12A3S2dS3cR7A2S8S0S14S47R10S13R10ReRcRbR2R1A6R3A3S28S2aR11A1R4RdRcR3R2A6S19S0S15R3A1S3eA3S22R6S13S2aR13A1R6RfReR5R4A6A2S44G1S27VCST;VXGL;S2aR14A1M2A3R15G2R13S13G2R7R10RfR6R5A6S30S43VCST;VXGL;G1G2R13R7R11A7A8F_;F_;F_;F_;Fjv;Ft;Frho2;S1fSaRfS25SaS5S29SaA1S7G1A1M3S1ReRdA5S6S4G3S1A3RcRbA5R8A4F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii HBG HBIG. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix 2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A.Wai_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A.Dai_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A.Wbi_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A.Wci_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A.Certi_2A ok A Kc rho tp Q p n t jv Hii HKc Hok).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 2 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (triple_pre_pure segsA ok _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instG_facts true (Wcan 2) UStopLe NVN VFN (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_N A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true (Wcan 2) UStopLe HHI HBG). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (g_instantiate_mid true 2 UStopLe NVN VFN Wbm_N2 Wcm_N2 Wdm_N2 Fb_N2 XIm_N2 A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A1 rho2 p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl), E13; exact HBG).
  exact (free_spine_m_N2 (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR Hn1
           (hdf_N2_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ ok _ Hok Hokp) (hdf_N2_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ ok _ Hok Hokp) (hdf_N2_3 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ ok _ Hok Hokp) (hdf_N2_4 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR) (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.
Theorem efree_hi_ia0_N_2 : ltac2:(tb__ "0|4|
S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S43VCST;VXGL;U2M1R6R5R4R3A7S1dS3R6A1S2eS3dS2fR4Z10A2A2S19S11S18R9A1S12A3S2dS3cR5A2S8S0S14S47ReS13ReRcRaR9R2R1A6R3A3S28S2aRfA1R4RbRaR3R2A6S19S0S15R3A1S3eA3S22R6S13S2aR11A1R6RdRcR5R4A6A2S45G1S27VCST;VXGL;S2aR12A1M2A3G2R11S13G2R7ReRdR6R5A6S30S43VCST;VXGL;G1G2R11R7RfA7A7F_;F_;F_;F_;Fjv;Ft;Frho2;S1eSaS25SaS5S29SaA1S7G1A1M3S1RcRbA5S6S4G3S1A3RaR9A5R6A3F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii HBG HBIG. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix 2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A.Wai_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A.Dai_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A.Wbi_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A.Wci_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A.ECerti_2A A Kc rho tp Q p n t jv Hii HKc).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 2 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (etriple_pre_pure segsA _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instG_facts true (Wcan 2) UStopLe NVN VFN (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_N A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true (Wcan 2) UStopLe HHI HBG). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (g_instantiate_mid true 2 UStopLe NVN VFN Wbm_N2 Wcm_N2 Wdm_N2 Fb_N2 XIm_N2 A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A1 rho2 p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl), E13; exact HBG).
  exact (efree_spine_m_N2 (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR Hn1
           (hdfe_N2_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ _) (hdfe_N2_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ _) (hdfe_N2_3 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ _) (hdfe_N2_4 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ _)
           (HBIG rho2 t jv ML HTJ JM HR) (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End AN2.
End F0A_aN2.

(* [comment removed for export] *)
Module SegQCF_call.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SVar"; "valuation"; "SLit"; "eval"; "rw"; "rm"; "SAlu"; "ss_next"; "sprop"; "odefault"; "ss_objs"; "cell"; "holds"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "obj_range"; "ranges_disjoint"; "sprop_eqb"; "ss_facts"; "sv_eqb"; "tfact"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "@Corelib.Init.Datatypes"; "pair"; "prod"; "bool"; "list"; "nat"; "cons"; "nil"; "true"; "option"; "andb"; "app"; "length"; "None"; "Some"; "fst"; "snd"; "false"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "of_nat"; "opp"; "leb"; "eqb"; "ltb"; "modulo"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "cls_of"; "QW"; "QFP"; "q_pure"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "rho_sub"; "in_ranges"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "qbatch"; "topG"; "aa_cache_inited"; "cs_cache"; "class_state"; "cs_mapped_free_array"; "aa_q_global"; "aa_q_thread"; "ag_spacebeg"; "budget_bound"; "cs_allocated_user"; "cs_free_array"; "mkQB"; "aa_cls"; "ag_ctx"; "ag_thread"; "ageom"; "cs_mapped_user"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "cell_ok"; "mkACell"; "maskv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lc.SegQCF_states"; "C1"; "RF"; "PreD"; "sF"; "PostD"; "T1f"; "pcbF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states"; "QG"; "DEPTH_R"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ"; "K0"; "AInvQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv"; "JRI"; "QP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "cells_inside"; "carved"; "lit_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel"; "drain_grows"; "drainA"; "drain_cs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ls.SegQCF_call"; "FLOC"; "fr_ok"; "stk_shapeb"; "ENVC"; "obj_spec"; "cells_insideb"; "cells_spec"; "gmaxS"; "mtxS"; "NRO"; "szS"; "@Corelib.Lists.ListDef"; "Forall"; "firstn"; "map"; "nth"; "skipn"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS"; "JLD"; "JD"; "drain_zone"; "O_dstD"; "dst_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states"; "clsB";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "J_ofPA"; "LQPA"; "import_okPA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Size"; "kFreeArraySize"; "kQuarantineMin"; "kSpaceSize"; "HIGH_SHADOW_END"; "IMG_HI"; "IMG_LO"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kFreeArrayMapSize"; "kUserSpaceSize"; "region_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "pre_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ls.SegQCF_call.GeoF"; "DZC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.SegQF_lib"; "DZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr"; "TR"; "TRP"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "fs_footb"; "geom_ok"; "inv3"; "secondary_repr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue"; "coverb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip"; "N_rti"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQS_glue SegQS_scan SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_drain DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SegQS_k OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvQ9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lc.SegQCF_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.SegQF_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.SegQCF_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQ7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition FLOC (A : AA) (z : Z) : Prop := ltac2:(tb__ "0|3|
S21S33S52S50VA;A1M0A1Vz;A2S21S1eS33SaaVz;A2S35Vz;Sa9A2A2S21S1eS33S5fG0A1M1Vz;A2S35Vz;S34G1Z1000A2A2A2S21S1eS33S34S60G0A1M2Z858A2Vz;A2S35Vz;S34G2Z860A2A2A2S1eS33S34G2Zad0A2Vz;A2S35Vz;S34G2Zc60A2A2A2A2A2A2A2").
Definition fr_ok (A : AA) (rho : valuation) (o : sobj) : Prop := ltac2:(tb__ "0|d|
S1fS3S3S1fS0S0S1fS0S0S1fS25S23S23S0S26A2M0S3A2M1A1M2G2S1eS1dS4Vo;S7dR4R3R2R1A4A3S1eS33S38S36Z2M3Z3fA2M4A1R3A2S1eS33R3R2A2S1eS35R2G4A2S1eS7cR3R2R1A3S1eS33Z0S34S41Q40M5S8Vrho;R4A2A2M6R3A2M7A2S1eS33S34G6R2A2S36G3Z40A2A2S1eS0S1eS33S34S41G5S8Vrho;R5A2A2M8R4A2R1A2S35R1S34G8R3A2A2A2M9S82VA;R2A2F_;Fz;S21S33S52S50VA;A1A1G7A2S21S0G9S1eS45VA;R2A2S20S1dS2aS3fQ8A1MaA1S63S3eSaVrho;A1MbR2A3S2eGaA1A3A1A2F_;Fz;S0G9S1fS0S0S1fS26S26S1fS3S3S1fS0S0S1eSb6G1S22G0S3S22S0S26R4R3A4R2A4R7A3S1eS1eS33S34S41G5S8Vrho;RaA2A2R4A2McR6A2S35R6S34GcS37R3A1A2A2A2S1eS1dS3fG5A1S8Vrho;R2A2S40G5R1A2A3S64S63S3eGbA2S65GcR3R1A3A2A2A2A2Lval;A2Le;A2Lk;A2Loff;A2F_;Fz;A2A2A2A2A2A2A2A2A2A2Lcs;A2Lhi;A2Llo;A2Lb;A2").

Lemma frame_view : ltac2:(tb__ "0|e|
S4fS4eS25S4A1M0G0S6S25S3fQ40M1A1M2A1S25S72A1M3S92S71S7bS3eR5R4R8S22G3S93R3S94R2R1A2A4A5S1dG0SfS4cR9A1A1S2cS4R8R7A3A3S8dS4S83RbR7A2R8A3S49R8R9S6eR4R7R5A3A3S6S1eS0S35R1S52S50ReA1A1A2S20S45RfR2A2A1S1dS2aS3fQ8A1M4A1M5S63S3eSaR4A1R3A3M6S63S3eSaRcA1R3A3A3F_;F_;Fz;S1eS0S45ReR1A2S20S1dG5S63S3eSaRbA1M7R2A3M8S2eG4A1M9A3A1S20S1dG5G6G9A3A1F_;F_;Fz;S1eS0S4Sb6S4R1RcA3S20S1eS33S30S0S0S17RcR2A2MaA3R3A2S35R3S31S0S0GaA3A2A2A1F_;Fo;S1dG5S63S3eSaR3A1MbR2A3G8A3F_;Fz;G2S4bRaRbR1A3S1eS82RfS41G1R2A2McA2S21S33S52S50RfA1A1GcA2S21S1eS45RfGcA2S20S1dG5S63S3eG7GcA3MdG9A3A1A2S1dG5S63S3eGbGcA3GdA3A2A2A2F_;Fa;A2A2A2Trho3;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;FR;Fobjs;FC;FA;").
Proof.
  intros A C objs R rho tp tr ms md Hsm0 HOBJ HFR rho3.
  pose proof (proj1 Hsm0) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  destruct (absorb_io rho R (vms md tp ms)) as [_ AOUT]. fold rho3 in AOUT.
  assert (INR : forall z, (0 <= z < 2 ^ 64 /\ in_ranges rho R (Z_to_bv 64 z)) ->
            exists b lo hi cs, In (carved b lo hi cs) R /\ - 2 ^ 63 <= lo /\ lo <= hi /\ hi < 2 ^ 63 /\ cells_inside lo hi cs
              /\ 0 <= bv_unsigned (eval rho b) + lo /\ bv_unsigned (eval rho b) + hi <= 2 ^ 64
              /\ bv_unsigned (eval rho b) + lo <= z < bv_unsigned (eval rho b) + hi /\ FLOC A z
              /\ (topG (aa_geom A) <= bv_unsigned (eval rho b) + lo
                  \/ (forall z, bv_unsigned (eval rho b) + lo <= z < bv_unsigned (eval rho b) + hi -> QW A z /\ view segsA (rm rho) z <> None)
                  \/ (forall z, bv_unsigned (eval rho b) + lo <= z < bv_unsigned (eval rho b) + hi ->
                        exists off k e val, In (off, k, e) cs /\ bv_unsigned (eval rho b) + off <= z < bv_unsigned (eval rho b) + off + Z.of_nat k
                           /\ eval rho e = Z_to_bv 64 val /\ cell_ok (view segsA (rm rho)) (mkACell (bv_unsigned (eval rho b) + off) k val)))).
  { intros z (Hr & o & Ho & Hz). rewrite u64_lit in Hz by exact Hr.
    destruct (proj1 (Forall_forall _ _) HFR o Ho) as (b & lo & hi & cs & -> & L1 & L2 & L3 & CI & B1 & B2 & LOC & ALT).
    unfold carved in Hz. rewrite obj_range_mk in Hz by lia. cbn [fst snd] in Hz.
    exists b, lo, hi, cs. repeat (split; [assumption|]). split; [exact (LOC z Hz) | exact ALT]. }
  assert (ROV : forall z b lo hi cs, In (carved b lo hi cs) R -> - 2 ^ 63 <= lo -> lo <= hi -> hi < 2 ^ 63 -> cells_inside lo hi cs ->
            0 <= bv_unsigned (eval rho b) + lo -> bv_unsigned (eval rho b) + hi <= 2 ^ 64 -> bv_unsigned (eval rho b) + lo <= z < bv_unsigned (eval rho b) + hi ->
            (forall z, bv_unsigned (eval rho b) + lo <= z < bv_unsigned (eval rho b) + hi ->
                        exists off k e val, In (off, k, e) cs /\ bv_unsigned (eval rho b) + off <= z < bv_unsigned (eval rho b) + off + Z.of_nat k
                           /\ eval rho e = Z_to_bv 64 val /\ cell_ok (view segsA (rm rho)) (mkACell (bv_unsigned (eval rho b) + off) k val)) ->
            view segsA (rm rho3) z = view segsA (rm rho) z).
  { intros z b lo hi cs HoR L1 L2 L3 CI B1 B2 Hzr ALT.
    destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) objs R b lo hi cs Hsm HOBJ HoR L1 L2 L3 CI B1 B2) as [AVc _]. fold rho3 in AVc.
    destruct (ALT z Hzr) as (off & k & e & val & Hin' & Hzc & Ee & Cv).
    pose proof (av_cell (view segsA (rm rho3)) (bv_unsigned (eval rho b)) off k e val rho (fun j Hj => AVc off k e j Hin' Hj) Ee) as C3.
    exact (cell_ok_same (view segsA (rm rho)) (view segsA (rm rho3)) _ Cv C3 z ltac:(cbn [c_addr c_w]; lia)). }
  split; [|split; [|split]].
  - intros z Hz NQ. destruct (IRdec rho R z) as [Hin|Hout]; [|exact (AOUT z Hout)].
    destruct (INR z Hin) as (b & lo & hi & cs & HoR & L1 & L2 & L3 & CI & B1 & B2 & Hzr & _ & [ALT|[ALT|ALT]]).
    + exfalso. lia.
    + exfalso. exact (NQ (proj1 (ALT z Hzr))).
    + exact (ROV z b lo hi cs HoR L1 L2 L3 CI B1 B2 Hzr ALT).
  - intros z HQ Hd. destruct (IRdec rho R z) as [Hin|Hout]; [|rewrite (AOUT z Hout); exact Hd].
    destruct (INR z Hin) as (b & lo & hi & cs & HoR & L1 & L2 & L3 & CI & B1 & B2 & Hzr & _ & _).
    destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) objs R b lo hi cs Hsm HOBJ HoR L1 L2 L3 CI B1 B2) as [_ PRc]. fold rho3 in PRc.
    destruct (PRc z Hzr) as [x Hx]. rewrite Hx. discriminate.
  - intros z HN. apply AOUT. intros (Hr & o & Ho & Hz). rewrite u64_lit in Hz by exact Hr. exact (HN o Ho Hz).
  - intros a Ha. pose proof (urange a) as Ra.
    destruct (INR (bv_unsigned a) ltac:(split; [exact Ra | rewrite Z_to_bv_bv_unsigned; exact Ha])) as (b & lo & hi & cs & HoR & L1 & L2 & L3 & CI & B1 & B2 & Hzr & LOC & [ALT|[ALT|ALT]]).
    + split; [exact LOC|]. left. lia.
    + split; [exact LOC|]. right; left. exact (ALT _ Hzr).
    + split; [exact LOC|]. right; right. exact (ROV _ b lo hi cs HoR L1 L2 L3 CI B1 B2 Hzr ALT).
Qed.

Fixpoint cells_spec (l : list cell) : option (list (Z * nat * sv)) :=
  match l with
  | [] => Some []
  | c :: t => match c_off c, cells_spec t with
              | SLit off, Some r => if ((1 <=? c_width c) && (c_width c <=? 8))%bool then Some ((off, Z.to_nat (c_width c), SymState.c_val c) :: r) else None
              | _, _ => None
              end
  end.
Lemma cells_spec_sound : ltac2:(tb__ "0|2|
S25S10A1M0S25S23S23S0S26A2S3A2A1M1S1dS2aG1A1S88R2A1S2fG1R1A2A3S1dG0R3S7eR2A1A3F_;Fcs;Fl;").
Proof.
  induction l as [|c t IH]; intros cs H; cbn [cells_spec] in H.
  - injection H as <-. reflexivity.
  - destruct c as [o w v]. cbn [c_off c_width SymState.c_val] in H. destruct o; try discriminate H. destruct (cells_spec t) as [r|]; [|discriminate H].
    destruct ((1 <=? w) && (w <=? 8))%bool eqn:EW; [|discriminate H]. injection H as <-. apply andb_true_iff in EW as (W1 & W2). apply Z.leb_le in W1, W2.
    cbn [lit_cells]. rewrite Z2Nat.id by lia. rewrite <- (IH r eq_refl). reflexivity.
Qed.
Definition cells_insideb (lo hi : Z) (cs : list (Z * nat * sv)) : bool := ltac2:(tb__ "0|2|
Sb7S23S23S0S26A2M0S3A2M1G1G1S24Lc;R1G0S3G0S24Lp;R2S0S26S2bS2bS2bS39Vlo;R2A2S39S34R2S37R1A1A2Vhi;A2A2Sb5U1R1A2A2Sb5R1U8A2A2Lk;Loff;X23x1Lv;Lp;X23x1Lc;Vcs;A3").
Lemma cells_insideb_sound : ltac2:(tb__ "0|0|
S0S0S25S23S23S0S26A2S3A2A1S1dS24S87R3R2R1A3S29A3S7cR4R3R2A3F_;Fcs;Fhi;Flo;").
Proof.
  intros lo hi cs H. unfold cells_inside. apply Forall_forall. intros [[off k] v] Hc. pose proof (proj1 (forallb_forall _ _) H _ Hc) as X. cbv beta iota in X.
  apply andb_true_iff in X as (X & X4). apply andb_true_iff in X as (X & X3). apply andb_true_iff in X as (X1 & X2).
  apply Z.leb_le in X1, X2. apply Nat.leb_le in X3, X4. lia.
Qed.
Definition obj_spec (o : sobj) : option carve_spec := ltac2:(tb__ "0|e|
S3S2aS42A1M0Lx;M1S16Vo;A1S0G1S15Vo;A1S0SeG0Lx;S14Vo;A1S2aS25S23S23S0S26A2S3A2A1M2A1G0Lx;S88S13Vo;A1A1G2S24G0L_;S2bS2bS2bS39S38S36Z2Z3fA2M3A1R3A2S39R3R2A2A2S3bR2G3A2A2S87R3R2R1A3A2S2fS23S23S23S3S0A2M4S0A2M5G2A2S22G5G2S22G4S0S22S3S0S12Vo;A1R3A4R2A4R1A4A2S2eS42A1M6X24x2Lcs;G6X2ax2G6G6S1G6Ll;M7G7S0S3S25S23S0S0A2A1S25S1cA1G6Ltmpl;Lflds;Lcnt;Lesz;Xex6Lhi;S1G6Li;M8S74S3S3G6Lb;La;M9Lop;MaGaS75G9Lop;MbGbS24S2S3G6La;Lw;Lsgn;McS1S3S0G6Lk;Li;Ll;MdX3x8Llo;G8GaGaGbGbGcGdX3x8").
Lemma obj_spec_sound : ltac2:(tb__ "0|4|
S4S3S0S0S25S23S23S0S26A2S3A2A1M0S1dS2aS42A1S86R5A1S2fS23S23S23S3S0A2M1S0A2M2G0A2S22G2G0S22G1S0S22S3S0R4R3A4R2A4R1A4A2A3S1eS1dS4R6S7dR5R4R3R2A4A3S1eS33S38S36Z2Z3fA2M3A1R4A2S1eS33R4R3A2S1eS35R3G3A2S7cR4R3R2A3A2A2A2A2F_;Fcs;Fhi;Flo;Fb;Fo;").
Proof.
  intros [ob ol oh oc od] b lo hi cs H. unfold obj_spec in H. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in H.
  destruct ol; try discriminate H. destruct oh; try discriminate H. destruct od; try discriminate H. destruct (cells_spec oc) as [r|] eqn:EC; [|discriminate H].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:EB; [|discriminate H] end. injection H as <- <- <- <-.
  apply andb_true_iff in EB as (EB & B4). apply andb_true_iff in EB as (EB & B3). apply andb_true_iff in EB as (B1 & B2).
  apply Z.leb_le in B1, B2. apply Z.ltb_lt in B3. unfold carved. rewrite (cells_spec_sound oc r EC).
  split; [reflexivity|]. split; [exact B1|]. split; [exact B2|]. split; [exact B3 | exact (cells_insideb_sound _ _ _ B4)].
Qed.

Lemma fr_ok_stack : ltac2:(tb__ "0|4|
S4fS6S4S3S0S0S25S23S23S0S26A2S3A2A1M0S1dS2aS42A1S86R5A1S2fS23S23S23S3S0A2M1S0A2M2G0A2S22G2G0S22G1S0S22S3S0R4R3A4R2A4R1A4A2A3S33S52S50R8A1A1S34S41Q40M3S8R7R5A2A2R4A2A2S33S34S41G3S8R8R6A2A2R4A2S36Z2Z40A2A2S83RaR9R8A3F_;F_;F_;Fcs;Fhi;Flo;Fb;Fo;Frho;FA;").
Proof.
  intros A rho o b lo hi cs HS H1 H2. destruct (obj_spec_sound o b lo hi cs HS) as (-> & L1 & L2 & L3 & CI). pose proof (topG_range (aa_geom A)) as TG.
  exists b, lo, hi, cs. split; [reflexivity|]. split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact CI|]. split; [lia|]. split; [exact H2|].
  split; [intros z Hz; left; lia|]. left. exact H1.
Qed.
Definition stk_shapeb (o : sobj) (k : sv * Z * Z) : bool := ltac2:(tb__ "0|4|
S2aS42A1S24Lx;S86Vo;A1S42S23S23S23S3S0A2M0S0A2M1S25S23S23S0S26A2S3A2A1M2A2S24Lc;R1G1G2G1S24Lp;R2G0S0G0S24Lp0;R2S3S0S2bS2bS1bS30S3S0S30G0S0Vk;A3M3A3R2A2S3aS31S3S0G3A3R1A2A2S3aS31G0S0Vk;A3R3A2A2Llo';Lb';X23x1Lhi';Lp0;X23x1Ll;Lp;X23x1Lc;S32X2ax2").
Lemma stk_shapeb_sound : ltac2:(tb__ "0|3|
S4S3S0S0S1dS24S84R4S22S23S3S0A2M0S0S22S3S0R3R2A4R1A4A2S29A3S1fS25S23S23S0S26A2S3A2A1M1G1S1dS2aS42A1S86R6A1S2fS23S23G0S0A2M2G1A2S22G2G1S22G0S0S22S3S0R5R4A4R3A4R1A4A2A3Lcs;A2F_;Fhi;Flo;Fb;Fo;").
Proof.
  intros o b lo hi H. unfold stk_shapeb in H. destruct (obj_spec o) as [[[[b' lo'] hi'] cs]|]; [|discriminate H]. cbn [fst snd] in H.
  apply andb_true_iff in H as (H & H3). apply andb_true_iff in H as (H1 & H2). apply sv_eqb_sound in H1. apply Z.eqb_eq in H2, H3. subst. exists cs. reflexivity.
Qed.

Definition STKF : list (sv * Z * Z) := ltac2:(tb__ "0|6|
S27S23S23S3S0A2M0S0A2M1S22G0S0S22S3S0SbS73S5PaA1M2S7Nc0M3A1A3N30A4Z0M4A4S27G1S22G0S0S22S3S0G2G3A4Nb8M5A4S27G1S22G0S0S22S3S0SbS73G2S7G5A1A3G4A4Z10A4S27G1S22G0S0S22S3S0G2Na8A4G4A4S28G1A1A3A3A3A3").
Definition mtxS : carve_spec := ltac2:(tb__ "0|6|
S22S23S23S3S0A2M0S0A2S25S23S23S0S26A2M1S3A2M2A1S22G0S0S22S3S0S7Z0A1M3S34S6fZ98A2M4A4S34S6fZ9cA2A4S27G2S22G1S3S22S0S26S34S6fZ99A2U1M5A4G3A4S27G2S22G1S3S22S0S26G4G5A4G3A4S27G2S22G1S3S22S0S26S34S6fZ9aA2U2A4G3A4S28G2A1A3A3A3A4").
Definition gmaxS : carve_spec := ltac2:(tb__ "0|5|
S22S23S23S3S0A2M0S0A2S25S23S23S0S26A2M1S3A2M2A1S22G0S0S22S3S0S7Z0A1S34S6fZ40A2M3A4S34S6fZ50A2A4S27G2S22G1S3S22S0S26G3U8M4A4S7Z10000000A1A4S27G2S22G1S3S22S0S26S34S6fZ48A2G4A4S5Pd0A1A4S28G2A1A3A3A4").
Definition szS : carve_spec := ltac2:(tb__ "0|4|
S22S23S23S3S0A2M0S0A2S25S23S23S0S26A2M1S3A2M2A1S22G0S0S22S3S0S6dZ8M3A4Z10A4S27G2S22G1S3S22S0S26G3U8A4S5Pc9A1A4S28G2A1A3A4").
Definition NRO (g : bool) : list carve_spec := ltac2:(tb__ "0|d|
S24S25S42A1Lg;Vg;S27S42S8aS27S42S89S27S42S8cS28S42A1M0A3M1A3A3S2cS42S27S42S8aS27S42S89G0A3A3S2cS42S91S42U2Sc2A3S27S23S23S23S3S0A2M2S0A2M3S25S23S23S0S26A2M4S3A2M5A1M6A2M7S22G3G6S22G2S0S22S3S0S7Z0A1M8Z17fcecM9A4Z17fcedA4S27G5S22G4S3S22S0S26G9U1A4G8A4S28G5A1MaA3A4S27G7S22G3G6S22G2S0S22S3S0G8Z17fc78MbA4Z17fc80A4S27G5S22G4S3S22S0S26GbU8McA4G8A4GaA3A4S27G7S22G3G6S22G2S0S22S3S0SbcZad0A4Zc60A4S27G5S22G4S3S22S0S26Zae0GcA4S5Pd1A1A4GaA3A4G1A3A3A3A3A3X24x2").
Lemma RF_shape : ltac2:(tb__ "0|1|
S24S1dS25S4A1S68R1A1M0S2cS4S8eS4U4G0A3S8fS42S4S43S8bR1A1A4A3A3Fg;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma RF_stk : ltac2:(tb__ "0|5|
S24S1fS4S4S1fS4S4S1fS4S4S1fS4S4S1eS1dS25S4A1S8eS4U4S68R5A1A3S27S4R4S27S4R3S27S4R2S27S4R1S28S4A1A3A3A3A3A3S1eS1dS24S84R4S22S23S3S0A2M0S0S22S3S0SbS73S5PaA1M1S7Nc0M2A1A3N30A4Z0M3A4A2S29A3S1eS1dS24S84R3S22G0S0S22S3S0G1G2A4Nb8M4A4A2S29A3S1eS1dS24S84R2S22G0S0S22S3S0SbS73G1S7G4A1A3G3A4Z10A4A2S29A3S1dS24S84R1S22G0S0S22S3S0G1Na8A4G3A4A2S29A3A2A2A2A2Lo4;A2Lo3;A2Lo2;A2Lo1;A2Fg;").
Proof. intros [|]; do 4 eexists; (split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]); repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C1_objs : ltac2:(tb__ "0|1|
S24S1dS25S4A1SfS4cS67R1A1A1A1M0S2cS4S8eS4S24S26Lg;R1U16UbX24x2G0A3S68R1A1A3A3Fg;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma fr_ok_ro : ltac2:(tb__ "0|c|
S4fS6S3S0S0S25S23S23S0S26A2M0S3A2M1A1M2S0S1dS3fQ40M3A1M4S8R6R5A2S40G3R1A2M5A3S1eS33Z0M6R2A2S35R2S36Z2M7Z40A2M8A2A2S33S38S36G7Z3fA2M9A1R6A2S33R7R6A2S35R7G9A2S7cR9R8R7A3S33G6S34R7RaA2A2S33S34R8RaA2G8A2S0S1eS33S34RaRdA2R1A2S35R1S34RaRcA2A2A2S82R11R2A2F_;Fz;S1dS24Sc1S22S23S23S3S0A2MaS0A2MbG2S22GaS0S22S3S0ReRdA4RcA4RbA4A1S29A3S8dG1G1G1OLc;R1G0S3G0OLp;R2S0S26S1fS0S0S1eS1dG4S8R16R4A2G5A3S64S63S3eSaR16A1A2S65S34R11R3A2R2R1A3A2A2Lval;A2Lk;Loff;X23x1Le;Lp;X23x1Lc;RcA3S83R12R11S43S22GbG2S22GaS0S22S3S0R10RfA4ReA4RdA4A1A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fa0;Fcs;Fhi;Flo;Fb;Frho;FA;").
Proof.
  intros A rho b lo hi cs a0 Eb H0 H1 H2 H3 CI H4 H5 LOC HC HF. exists b, lo, hi, cs. rewrite Eb, u64_lit by exact H0.
  split; [reflexivity|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact CI|]. split; [exact H4|]. split; [exact H5|]. split; [exact LOC|]. right; right.
  intros z Hz. destruct (SMGlue.coverb_sound _ HC (z - a0) ltac:(lia)) as (o & n & e & Hin & Ho).
  pose proof (proj1 (Forall_forall _ _) HF _ Hin) as X0. cbv beta iota in X0. destruct X0 as (val & Ev & Cv).
  exists o, n, e, val. split; [exact Hin|]. split; [lia|]. split; [exact Ev | exact Cv].
Qed.
Lemma fr_ok_qw : ltac2:(tb__ "0|8|
S4fS6S3S0S0S25S23S23S0S26A2S3A2A1M0S0S1dS3fQ40M1A1S8R6R5A2S40G1R1A2A3S1eS33Z0M2R2A2S35R2S36Z2M3Z40A2M4A2A2S33S38S36G3Z3fA2M5A1R6A2S33R7R6A2S35R7G5A2S7cR9R8R7A3S33G2S34R7RaA2A2S33S34R8RaA2G4A2S0S1eS33S34RaRdA2R1A2S35R1S34RaRcA2A2A2S82R11R2A2F_;Fz;S0S1eS33S34RbReA2R1A2S35R1S34RbRdA2A2A2S1eS45R12R2A2S20S1dS2aS3fQ8A1M6A1S63S3eSaR11A1R2A3S2eG6A1A3A1A2F_;Fz;S83R11R10S43S22S23S23S3S0A2M7S0A2G0S22G7S0S22S3S0RfReA4RdA4RcA4A1A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fa0;Fcs;Fhi;Flo;Fb;Frho;FA;").
Proof.
  intros A rho b lo hi cs a0 Eb H0 H1 H2 H3 CI H4 H5 LOC HQ. exists b, lo, hi, cs. rewrite Eb, u64_lit by exact H0.
  split; [reflexivity|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact CI|]. split; [exact H4|]. split; [exact H5|]. split; [exact LOC|]. right; left. exact HQ.
Qed.

Ltac rtc_cell HR := first [ exact (cells_ok_nth _ _ 0%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 1%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 2%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 3%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 4%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 5%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 6%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 7%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 8%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 9%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 10%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 11%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 12%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 13%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 14%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 15%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 16%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 17%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 18%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 19%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 20%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 21%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 22%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 23%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 24%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 25%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 26%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 27%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 28%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 29%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 30%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 31%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 32%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 33%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 34%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 35%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 36%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 37%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 38%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 39%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 40%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 41%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 42%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 43%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 44%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 45%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 46%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 47%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 48%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 49%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 50%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 51%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 52%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 53%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 54%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 55%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 56%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 57%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 58%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 59%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 60%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 61%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 62%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 63%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 64%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 65%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 66%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 67%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 68%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 69%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 70%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 71%nat _ HR eq_refl) ].
Section FrameF.
Variables (Kc : KcA) (A : AA) (r : valuation) (tp : list word) (tr : list event) (md : Model).
Hypothesis HKc : Kc_ok Kc.
Hypothesis HK : ltac2:(tb__ "0|0|
S76VKc;VA;Vr;Vtp;Vtr;Vmd;A6").
Hypothesis HCI : aa_cache_inited A = true.
Hypothesis HFp : ltac2:(tb__ "0|0|
S8dSdS11Vr;A1Sb0S70A1A3").
Hypothesis EC : ltac2:(tb__ "0|1|
S1dS3fQ40M0A1S8Vr;S9dA2S40G0Z18A2A3").
Hypothesis E201 : ltac2:(tb__ "0|1|
S1dS3fQ40M0A1S9Vr;Pc9A2S40G0Sa4Z18A1A2A3").
Hypothesis E208 : ltac2:(tb__ "0|1|
S1dS3fQ40M0A1S9Vr;Pd0A2S40G0Sa6A2A3").

Lemma fr_all : ltac2:(tb__ "0|0|
S24S8dS4S83VA;Vr;A2S68R1A1A3Fg;").
Proof using All.
  intros g. pose proof (K0_laws Kc HKc) as HL.
  destruct (kq_facts segsA (K0 Kc) HL A r tp _ _ HK) as [HG HRIG HRTC HMIN HST _ HCLS _ _ _ _ _ _].
  destruct HRIG as (E151 & E152 & E155 & E156).
  pose proof HK as (_ & _ & _ & HTOP & _).
  destruct (stk_facts A r HTOP HFp) as (HD & HT2 & HSP). cbv zeta in HD, HT2, HSP.
  pose proof (HCLS HCI 24 ltac:(lia)) as CV. pose proof (cv_size _ _ _ _ _ CV) as C_sz. unfold pc_entry in C_sz. change (Size 24) with 8192 in *.
  pose proof (geom_nums _ HG) as (_ & _ & _ & T0 & T1 & _ & C0 & C1' & _ & _ & S1 & S2 & S16 & TG).
  assert (HR : cells_ok (view segsA (rm r)) (rtc_cells RTC_A (aa_geom A))) by exact HRTC.
  set (T := ag_thread (aa_geom A)) in *. set (CTX := ag_ctx (aa_geom A)) in *.
  assert (EcbC : eval r cbC = Z_to_bv 64 (T + 208)) by (unfold cbC; apply ev_add_lit; [unfold vT; cbn [eval]; exact E151 | lia | lia | lia]).
  assert (Epcb : eval r pcbF = Z_to_bv 64 (T + 2128)).
  { apply bv_eq. unfold pcbF, add. rewrite U_add, U_mul. fold (add vT (SLit 208)). fold cbC. rewrite EcbC, EC. change (eval r (SLit 80)) with (Z_to_bv 64 80). rewrite !u64_lit by lia. unfold M64v.
    rewrite (Z.mod_small (24 * 80)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (E10a : bv_unsigned (eval r (SAlu ALU_ADD (SVar 10) (SLit (-192)))) = bv_unsigned (rw r 10%positive) - 192).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-192))) with (2 ^ 64 - 192) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (E10b : bv_unsigned (eval r (SAlu ALU_ADD (SVar 10) (SLit (-184)))) = bv_unsigned (rw r 10%positive) - 184).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-184))) with (2 ^ 64 - 184) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  rewrite RF_shape. apply Forall_app. split.
  -
    destruct (RF_stk g) as (o1 & o2 & o3 & o4 & -> & S1' & S2' & S3' & S4').
    destruct (stk_shapeb_sound _ _ _ _ S1') as (c1 & Q1). destruct (stk_shapeb_sound _ _ _ _ S2') as (c2 & Q2).
    destruct (stk_shapeb_sound _ _ _ _ S3') as (c3 & Q3). destruct (stk_shapeb_sound _ _ _ _ S4') as (c4 & Q4).
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (fr_ok_stack A r o1 _ _ _ _ Q1); rewrite E10a; lia.
    + apply (fr_ok_stack A r o2 _ _ _ _ Q2); cbn [eval]; lia.
    + apply (fr_ok_stack A r o3 _ _ _ _ Q3); rewrite E10b; lia.
    + apply (fr_ok_stack A r o4 _ _ _ _ Q4); cbn [eval]; lia.
  - assert (QM : fr_ok A r (carve_obj mtxS)).
    { unfold mtxS. apply (fr_ok_qw A r _ _ _ _ 0); try reflexivity; try (unfold QG; lia).
      - unfold cells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn; unfold QG; lia.
      - intros z Hz. right; left. unfold IMG_LO, IMG_HI. unfold QG in Hz. lia.
      - intros z Hz. split; [right; left; right; left; unfold Inv.QG; unfold QG in Hz; lia|].
        unfold QG in Hz. rewrite view_in by lia. destruct (rd_of_imageA (rm r) z ltac:(lia)) as [x Hx]. rewrite Hx. discriminate. }
    assert (QGM : fr_ok A r (carve_obj gmaxS)).
    { unfold gmaxS. apply (fr_ok_ro A r _ _ _ _ 0); try reflexivity; try (unfold QG; lia).
      - unfold cells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn; unfold QG; lia.
      - intros z Hz. right; left. unfold IMG_LO, IMG_HI. unfold QG in Hz. lia.
      - repeat apply Forall_cons; try apply Forall_nil; cbv beta iota.
        + exists kQuarantineMax. split; [reflexivity|]. unfold rtc_inv, rtc_cells in HRTC. exact (cells_ok_nth _ _ 7 _ HRTC eq_refl).
        + exists kQuarantineMin. split; [cbn [eval]; exact E208 | exact HMIN]. }
    assert (QSZ : fr_ok A r (carve_obj szS)).
    { unfold szS. apply (fr_ok_ro A r _ _ _ _ (T + 2128)); try reflexivity; try lia; [exact Epcb | | |].
      - unfold cells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn; lia.
      - intros z Hz. right; right; right; left. subst T. lia.
      - repeat apply Forall_cons; try apply Forall_nil; cbv beta iota. exists 8192. split; [cbn [eval]; exact E201|].
        replace (T + 2128 + 8) with (T + 208 + 80 * 24 + 8) by lia. exact C_sz. }
    unfold NRO. destruct g.
    + repeat apply Forall_cons; try apply Forall_nil; assumption.
    + cbn [app map]. apply Forall_cons; [exact QM|]. apply Forall_cons; [exact QGM|]. unfold N_rti. cbn [skipn app map].
      repeat apply Forall_cons; try apply Forall_nil; try exact QSZ.
      12: { apply (fr_ok_qw A r _ _ _ _ T); [exact E151 | lia | lia | lia | lia | unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia | lia | lia | |].
            - intros z Hz. right; right; right; right. subst T. lia.
            - intros z Hz. split; [right; right; unfold qstat_zone; subst T; lia|]. destruct (HST z ltac:(subst T; lia)) as [x Hx]. rewrite Hx. discriminate. }
      7: { apply (fr_ok_ro A r _ _ _ _ CTX); [exact E152 | lia | lia | lia | lia | unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia | lia | lia | | reflexivity |].
           - intros z Hz. right; right; left. subst CTX. lia.
           - repeat apply Forall_cons; try apply Forall_nil; cbv beta iota. exists T. split; [exact E151 | rtc_cell HR]. }
      all: apply (fr_ok_ro A r _ _ _ _ 0); [reflexivity | lia | lia | lia | lia | unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia | lia | lia | intros z Hz; right; left; unfold IMG_LO, IMG_HI; lia | reflexivity |].
      all: repeat apply Forall_cons; try apply Forall_nil; cbv beta iota; eexists; (split; [first [reflexivity | exact E152]|]); rtc_cell HR.
Qed.
End FrameF.

Section GeoF.
Variables (Kc : KcA) (A : AA) (r : valuation) (tp : list word) (tr : list event) (md : Model).
Hypothesis HKc : Kc_ok Kc.
Hypothesis HK : ltac2:(tb__ "0|0|
S76VKc;VA;Vr;Vtp;Vtr;Vmd;A6").
Let G := aa_geom A.
Let T := ag_thread G.
Let SB := ag_spacebeg G.

Definition DZC (z : Z) : Prop := ltac2:(tb__ "0|0|
S21S1eS33S34VT;Z850A2Vz;A2S35Vz;S34VT;Z854A2A2A2S21S1eS33VSB;Vz;A2S35Vz;S34S34VSB;Sa7A2Z1000A2A2A2S1eS33SacVz;A2S35Vz;SabA2A2A2A2").

Lemma geo_nums : ltac2:(tb__ "0|0|
S1eS33Sa8VSB;A2S1eS33S34S34VSB;Sa7A2Z1000A2S52VG;A1A2S1dS0S3cVSB;Z8A2Z0A3A2A2").
Proof using HKc HK.
  pose proof (K0_laws Kc HKc) as HL. destruct (kq_facts segsA (K0 Kc) HL A r tp _ _ HK) as [HG _ _ _ _ _ _ _ _ _ _ _ _]. fold G in HG.
  pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & S16 & TG). fold G SB in S1, S2, S16.
  split; [exact S1|]. split; [rewrite kSpaceSize_val; rewrite kSpaceSize_val in S2; lia|]. change (2 ^ 16) with (8 * 8192) in S16.
  rewrite <- (Z.mod_mod_divide SB (8 * 8192) 8) by (exists 8192; lia). rewrite S16. reflexivity.
Qed.

Lemma floc_out : ltac2:(tb__ "0|0|
S0S82VA;R1A2S20Sb1R2A1A1F_;Fz;").
Proof using HKc HK.
  pose proof (K0_laws Kc HKc) as HL. destruct (kq_facts segsA (K0 Kc) HL A r tp _ _ HK) as [HG _ _ _ _ _ _ _ _ _ HSEP3 _ _]. fold G in HG, HSEP3.
  pose proof (geom_nums _ HG) as (_ & _ & _ & T0 & T1 & _ & C0 & C1' & _ & _ & S1 & S2 & _ & TG). fold G T SB in T0, T1, S1, S2.
  pose proof (geom_bands _ HG) as (_ & _ & _ & _ & TI & CI & _). fold G T in TI. pose proof (geom_seps _ HG) as (_ & _ & _ & _ & Q5 & _). fold G T in Q5.
  destruct HSEP3 as (P1 & P2 & _). fold G T SB in P1, P2.
  assert (CB : ag_ctx G + 0x1000 <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= ag_ctx G) by (destruct HG as (_ & _ & _ & (_ & _ & _ & _ & X0) & _); exact X0).
  assert (TB : T + 0x1000 <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= T) by (destruct HG as (_ & _ & (_ & _ & _ & _ & _ & X0) & _); exact X0).
  unfold IMG_LO, IMG_HI, HIGH_SHADOW_END, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG in *. rewrite kSpaceSize_val in *.
  intros z HF HZ. unfold FLOC in HF. fold G T in HF. unfold DZC in HZ. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG in *. unfold HIGH_SHADOW_END, IMG_LO, IMG_HI in *. rewrite kSpaceSize_val in HZ. lia.
Qed.

Lemma dzone_coarse : ltac2:(tb__ "0|1|
S0S9aVG;Z18M0S44VA;G0A2R1A4S1dS24S53VA;A1S29A3Sb1R3A1F_;F_;Fz;").
Proof using HKc HK.
  intros z HZ HCI. pose proof (K0_laws Kc HKc) as HL. destruct (kq_facts segsA (K0 Kc) HL A r tp _ _ HK) as [HG _ _ _ _ _ HCLS _ _ _ _ _ _]. fold G in HG, HCLS.
  pose proof (HCLS HCI 24 ltac:(lia)) as CV. pose proof (cv_fa_bounds _ _ _ _ _ CV) as (FB1 & FB2 & FB3).
  destruct geo_nums as (S1 & S2 & S8). pose proof (topG_range G) as TG. pose proof (Zle_0_nat (length (cs_free_array (SegQ_wf2.cls_of A 24)))) as NF0.
  unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS.drain_zone in HZ. cbv zeta in HZ. fold T SB in HZ. change (kchunks 24) with 1 in HZ.
  unfold DZC. unfold free_array, region_beg, region_info, kUserSpaceSize, kRegionSize, kFreeArraySize, kFreeArrayMapSize, kRegionInfoStride, HIGH_SHADOW_END in *. rewrite kSpaceSize_val in *.
  destruct HZ as [H|[H|[H|(_ & [H|H])]]].
  - left. lia.
  - right; left. lia.
  - right; left. lia.
  - right; left. lia.
  - right; right. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, Sh, SHADOW_OFF in *.
    set (x := SB + 24 * 2 ^ 32 + (2 ^ 32 - 2 ^ 29) + cs_mapped_free_array (SegQ_wf2.cls_of A 24)) in *.
    pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as D0.
    pose proof (Z.div_le_upper_bound x 8 (2 ^ 44 - 32768) ltac:(lia) ltac:(lia)) as D1. lia.
Qed.
End GeoF.

Lemma sF_get : ltac2:(tb__ "0|d|
S24S1eS1dS3S48S6aR1A1M0PaM1A2SbS73S5G1A1S7Nf0A1A3A3S1eS1dS3S48G0PfM2A2SbS73S5G2A1S7Zf0A1A3A3S1eS1dS3S48G0P18M3A2S24S3Lg;R1S5G3A1S7SbbA1X24x2A3S1eS1dS3S48G0P97M4A2S5G4A1A3S1eS1dS3S48G0P98M5A2S5G5A1A3S1eS1dS3S48G0P9bM6A2S5G6A1A3S1eS1dS3S48G0P9cM7A2S5G7A1A3S1eS1dS3S48G0P9eA2S9dA3S1eS1dS3S48G0P94A2S7Z2000A1A3S1eS1dS3S48G0PaaA2S5Pe7A1A3S1eS1dS3S48G0PddM8A2S5G8A1A3S1eS1dS3S48G0PdeM9A2S5G9A1A3S1eS1dS3S48G0PdfMaA2S5GaA1A3S1eS1dS3S48G0Pe0MbA2S5GbA1A3S1dS3S48G0Pe1McA2S5GcA1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2Fg;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma C1_pre : ltac2:(tb__ "0|0|
S24S1dS24Sb7SdSdSb8SdS19R1A1S1aS4cS67R2A1A1A1A3Lf;Sb0S70A1A3S29A3Fg;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition ENVC (A : AA) (r : valuation) : Prop := ltac2:(tb__ "0|3|
S44VA;Z18M0A2S55S1eS1dS3fQ40M1A1M2S8Vr;S9dA2S40G1G0A2A3S1eS1dG2S9Vr;Pc9A2S40G1Sa4G0A1A2A3S1eS1dG2S9Vr;Pd0A2S40G1Sa6A2A3S1eS1dG2S9Vr;PddA2S40G1S37S2dS0S5cR1A1A2A1A2A3S1eS1dG2S9Vr;PdeA2S40G1S56R1A1A2A3S1eS1dG2S9Vr;PdfA2S40G1S5bR1A1A2A3S1eS1dG2S9Vr;Pe0A2S40G1S62R1A1A2A3S1eS1dG2S9Vr;Pe1A2S40G1SafS59S50VA;A1A1G0A2A2A3S1dG2S9Vr;Pe7A2S40G1S90S0U1S54R1A1Z0A4A2A3A2A2A2A2A2A2A2A2Tcs;").

Section CallF.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variables (A0 : AA) (rho0 : valuation).

Lemma qcf_JP : ltac2:(tb__ "0|3|
S24S4fS0S0S26S25S51A1M0G0S6S25S3fQ40A1A1S25S72A1M1S92S71S1dS24S53RbA1S29A3S1dS0S37S2dS0S54S44RcZ18M2A2A1A2A1Z2A3S1dS24S7fG2S44RdG2A2A2ReA3S85ReR8A2S7bS3eR9R8S67R10A1S22G1S93R7S94R6R5A2A4A5S78S76VKc;A1VA0;Vrho0;R10RfReRdS28S23S0S0A2A1RcRbRaR9R8R6AeS99Z1R12R11VKc;G2S4aS49RbS68R12A1S6eR7RaR8A3A3S6aR12A1A2RaR9R7A9F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Frest;Ftmp';Fnd;Fn0;Fa;FA;Fg;").
Proof.
  intros g A a n0 nd tmp' rest rho tp tr ms md HCI HFULL HGR (EC & E201 & E208 & E221 & E222 & E223 & E224 & E225 & E231) Hsm (HK & _).
  destruct (sF_get g) as (W10 & W15 & W24 & W151 & W152 & W155 & W156 & W158 & W148 & W170 & W221 & W222 & W223 & W224 & W225).
  pose proof (smatch_facts_hold _ _ _ _ (proj1 Hsm)) as HFa.
  assert (HFp : Forall (holds rho) (pre_facts DEPTH_R)).
  { apply Forall_forall. intros f Hf. pose proof (proj1 (forallb_forall _ _) (C1_pre g) f Hf) as X. apply existsb_exists in X as (f' & Hf' & E). apply sprop_eqb_sound in E. subst f'.
    exact (proj1 (Forall_forall _ _) HFa f Hf'). }
  set (r3 := rho_absorb rho (RF g) (vms md tp ms)).
  destruct (frame_view A (C1 g) _ (RF g) rho tp tr ms md Hsm (C1_objs g) (fr_all Kc A rho tp tr md HKc HK HCI HFp EC E201 E208 g)) as (FV1 & FV2 & _). fold r3 in FV1, FV2.
  assert (HK3 : K0 Kc A r3 tp tr md) by (apply (K0_blind Kc A rho r3 tp tr md); [intros i; reflexivity | intros l; reflexivity | exact FV1 | exact FV2 | exact HK]).
  destruct HK3 as (HA3 & HKc3 & Htp3 & Htop3 & HRG3).
  pose proof (K0_laws Kc HKc) as HL. destruct (kq_facts segsA (K0 Kc) HL A rho tp _ _ HK) as [HG _ _ _ _ _ _ _ _ _ _ _ _].
  pose proof HK as (_ & _ & _ & HTOP & _). destruct (stk_facts A rho HTOP HFp) as (HD & HT2 & HSP). cbv zeta in HD, HT2, HSP. pose proof (topG_range (aa_geom A)) as TG.
  split.
  - split; [exact HA3|]. split; [exact HKc3|]. split; [|split].
    + unfold tp_ok. cbn [rw rho_sub]. rewrite W24. destruct g; cbn [eval]; [exact Htp3|]. rewrite (proj1 (proj2 HG)). reflexivity.
    + unfold top_high, V_DEPTH. cbn [rw rho_sub]. rewrite W10, W15. unfold r3. rewrite !eval_absorb.
      assert (Em : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 10) (SLit (-240)))) = bv_unsigned (rw rho 10%positive) - 240).
      { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-240))) with (2 ^ 64 - 240) by reflexivity.
        rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
      rewrite Em. rewrite signed_add_lit by (cbn [eval]; unfold V_DEPTH in HD; lia). cbn [eval]. unfold V_DEPTH in HT2. lia.
    + unfold rigidQ. cbn [rw rho_sub]. rewrite W151, W152, W155, W156. cbn [eval]. exact HRG3.
  - unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS.dfacts. cbn [rw rho_sub]. change V_CLS with 158%positive. change V_SIZE with 148%positive. rewrite W158, W148, W221, W222, W223, W224, W225. unfold r3. rewrite !eval_absorb. cbn [eval].
    split; [exact HCI|]. split; [lia|]. split; [reflexivity|]. split; [exact HFULL|]. split; [exact HGR|]. split; [exact EC|]. split; [reflexivity|].
    split; [exact E221|]. split; [exact E222|]. split; [exact E223|]. split; [exact E224|]. split; [exact E225|].
    intros i Hi. change (Z.to_nat 1) with 1%nat in *. assert (i = 0%nat) by lia. subst i. change (Pos.of_nat (170 + 0)) with 170%positive. rewrite W170. cbn [eval rw rho_absorb]. exact E231.
Qed.

Lemma rd_pointwise : ltac2:(tb__ "0|0|
S0S0S0S0S0OF_;S0S1eS33R6R1A2S35R1R5A2A2R3R2A1F_;Fz;S0S1eS33R5R1A2S35R1R4A2A2S20R4R2A1A1F_;Fz;S18S22S0S0R5R4A4S22S0S0R7R6A4A2F_;F_;FP;Fe;Fd;Fh;Fl;").
Proof.
  intros l h d e P H1 H2. unfold SymState.ranges_disjoint. cbn [fst snd].
  destruct (Z_lt_dec d e) as [L1|L1]; [|left; lia]. destruct (Z_lt_dec l h) as [L2|L2]; [|right; left; lia].
  destruct (Z_le_dec e l) as [L3|L3]; [right; right; left; exact L3|]. destruct (Z_le_dec h d) as [L4|L4]; [right; right; right; exact L4|]. exfalso.
  destruct (Z_le_dec l d) as [L5|L5]; [exact (H2 d ltac:(lia) (H1 d ltac:(lia))) | exact (H2 l ltac:(lia) (H1 l ltac:(lia)))].
Qed.
Lemma newF' : ltac2:(tb__ "0|3|
S24S1dS25S4A1M0S97S4cS69R1A1A1S4cS6bR1A1A1A2S24G0Lg;R1S27S4S9bZ1M1S9cG1A1A2S28S4A1M2A3G2X24x2A3Fg;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XF0 : ltac2:(tb__ "0|4|
S24S1eS1dS25S23S3S3A2M0A1M1S4dS6bR1A1A1S28G0A1M2A3S1eS1dG1S4dS67R1A1M3A1G2A3S1eS1dG1S4dS6cR1A1A1G2A3S1eS1dS1ScS4cS69R1A1A1A1Pf0A3S1dS1ScS4cG3A1A1P104A3A2A2A2A2Fg;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma drainA_cls : ltac2:(tb__ "0|1|
S4fSb9U18S2dS55S5eR1A1A2A2S1dS55S44S80R2Z18M0A2G0A2S81G0S44R2G0A2A2A3F_;FA;").
Proof.
  intros A HL. unfold SegQ_wf2.cls_of, nthZ, drainA. cbn [aa_cls]. change (Z.to_nat 24) with 24%nat. apply nth_list_upd_same. exact HL.
Qed.

Lemma qcf_post_ok : ltac2:(tb__ "0|4|
S24S4fS0S0S26S25S51A1M0G0S6S25S3fQ40A1A1M1S25S72A1M2S92S71S6G1G2S71S1dS24S53RfA1S29A3S1dS0S37S2dS0S54S44R10Z18M3A2A1A2A1Z2A3S1dS24S7fG3S44R11G3A2A2R12A3S85R12RcA2S7bS3eRdRcS67R14A1S22G2S93RbS94RaR9A2A4A5S78S76VKc;A1VA0;Vrho0;R14R13R12R11S28S23S0S0A2A1R10RfReRdRcRaAeS95ScS4cS69R16A1A1A1S4aS49RfS68R16A1S6eRbReRcA3A3S6aR16A1A2RaA3S98R16VKc;G3S4aS49R10S68R17A1S6eRcRfRdA3A3S6aR17A1A2RfRbRaR9R8A9Sa1R11S6eRdR10ReA3S68R18A1S6aR18A1S69R18A1S6bR18A1S67R18A1RcA8F_;F_;F_;F_;F_;F_;F_;F_;Fmd';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;Ftp;Frho;Frest;Ftmp';Fnd;Fn0;Fa;FA;Fg;").
Proof.
  intros g A a n0 nd tmp' rest rho tp tr ms md rhoL tpL tr' md' HCI HFULL HGR (EC & E201 & E208 & E221 & E222 & E223 & E224 & E225 & E231) Hsm (HK & _) Hag (HKL & HRM & _).
  destruct (sF_get g) as (W10 & W15 & W24 & W151 & W152 & W155 & W156 & W158 & W148 & W170 & W221 & W222 & W223 & W224 & W225).
  destruct (XF0 g) as (XP & XC & _ & NXP & _).
  pose proof (smatch_facts_hold _ _ _ _ (proj1 Hsm)) as HFa.
  assert (HFp : Forall (holds rho) (pre_facts DEPTH_R)).
  { apply Forall_forall. intros f Hf. pose proof (proj1 (forallb_forall _ _) (C1_pre g) f Hf) as X. apply existsb_exists in X as (f' & Hf' & E). apply sprop_eqb_sound in E. subst f'.
    exact (proj1 (Forall_forall _ _) HFa f Hf'). }
  destruct (frame_view A (C1 g) _ (RF g) rho tp tr ms md Hsm (C1_objs g) (fr_all Kc A rho tp tr md HKc HK HCI HFp EC E201 E208 g)) as (_ & _ & _ & FR4).
  split; [split|split].
  - intros a0 Hin. apply HRM. intros HZ. exact (floc_out Kc A rho tp tr md HKc HK _ (proj1 (FR4 a0 Hin)) (dzone_coarse Kc A rho tp tr md HKc HK _ HZ HCI)).
  - intros o' oR Ho' HoR. rewrite newF' in Ho'. destruct g; [|destruct Ho']. destruct Ho' as [<-|[]].
    pose proof (K0_laws Kc HKc) as HL. destruct (kq_facts segsA (K0 Kc) HL A rho tp _ _ HK) as [HG HRIG _ _ _ _ HCLS _ _ _ _ _ _].
    destruct HRIG as (E151 & E152 & E155 & E156).
    pose proof (HCLS HCI 24 ltac:(lia)) as CV. pose proof (cv_fa_bounds _ _ _ _ _ CV) as (FB1 & FB2 & FB3).
    destruct (geo_nums Kc A rho tp tr md HKc HK) as (S1 & S2 & S8). pose proof (topG_range (aa_geom A)) as TG. cbv zeta in S1, S2, S8.
    set (SB := ag_spacebeg (aa_geom A)) in *. set (nf := Z.of_nat (length (cs_free_array (SegQ_wf2.cls_of A 24)))) in *. assert (NF0 : 0 <= nf) by (unfold nf; lia).
    assert (EL : forall v, (v < 240)%positive -> rw rhoL v = eval rho (wsub_get (sF true) v)).
    { intros v Hv. rewrite <- (proj1 Hag v ltac:(rewrite NXP; exact Hv)). cbn [rw rho_sub]. apply eval_absorb. }
    assert (E155L : rw rhoL 155%positive = Z_to_bv 64 SB) by (rewrite (EL 155%positive eq_refl), W155; exact E155).
    assert (E158L : rw rhoL 158%positive = Z_to_bv 64 24) by (rewrite (EL 158%positive eq_refl), W158; exact EC).
    assert (E221L : rw rhoL 221%positive = Z_to_bv 64 nf) by (rewrite (EL 221%positive eq_refl), W221; exact E221).
    unfold HIGH_SHADOW_END, kFreeArraySize in *. rewrite kSpaceSize_val in S2.
    assert (FAv : free_array SB 24 = SB + 24 * 2 ^ 32 + 3758096384) by (unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize; lia).
    assert (Edst : bv_unsigned (eval rhoL dst_e) = free_array SB 24 + 4 * nf).
    { unfold dst_e, fa_e. rewrite U_add, U_add, U_add, !U_sll_lit. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.vSB, vNF. cbn [eval]. change V_CLS with 158%positive. rewrite E158L, E155L, E221L, !u64_lit by lia.
      change (32 mod 64) with 32. change (2 mod 64) with 2. unfold M64v. rewrite (Z.mod_small (24 * 2 ^ 32)) by lia. rewrite (Z.mod_small (24 * 2 ^ 32 + 3758096384)) by lia.
      rewrite (Z.mod_small (SB + (24 * 2 ^ 32 + 3758096384))) by lia. rewrite (Z.mod_small (nf * 2 ^ 2)) by lia. rewrite Z.mod_small by lia. rewrite FAv. lia. }
    destruct (proj1 (Forall_forall _ _) (fr_all Kc A rho tp tr md HKc HK HCI HFp EC E201 E208 true) oR HoR) as (b & lo & hi & cs & -> & L1 & L2 & L3 & CI & B1 & B2 & LOC & _).
    unfold O_dstD, carved. rewrite !obj_range_mk by lia. rewrite Edst.
    apply (rd_pointwise _ _ _ _ (FLOC A) LOC). intros z Hz HF. apply (floc_out Kc A rho tp tr md HKc HK z HF). right; left. fold SB. rewrite kSpaceSize_val. rewrite FAv in Hz. lia.
  - intros r0 a0 j oR Hr. rewrite XP in Hr. destruct Hr.
  - intros r0 a0 j Hr. rewrite XC in Hr. destruct Hr.
Qed.

Lemma dzone_DZ : ltac2:(tb__ "0|3|
S4fS0S33Z0M0S59S50R2A1A1A2S33G0S56S44R3Z18M1A2A1A2S33S3dZ4S34S37S2dS0S5cS44R4G1A2A1A2A1Z1A2A2Sa5A2S1dS24S7fG1S44R5G1A2A2S29A3S33S34S56S44R6G1A2M2A1SadA2Sa5A2F_;S9aS50R6A1G1G2R5A4Sb2R7G1R6A3F_;F_;F_;F_;F_;Fz;FA;").
Proof.
  intros A z HSB HM0 HN HGRW HZ. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS.drain_zone in HZ. cbv zeta in HZ. change (kchunks 24) with 1 in HZ. unfold DZ. cbv zeta.
  pose proof (Zle_0_nat (length (cs_free_array (SegQ_wf2.cls_of A 24)))) as NF0.
  unfold kRegionInfoStride, kFreeArraySize, kFreeArrayMapSize in *.
  destruct HZ as [H|[H|[H|(HGW & [H|H])]]].
  - left. lia.
  - right; right; left. lia.
  - right; left. lia.
  - specialize (HGRW HGW). right; right; left. lia.
  - specialize (HGRW HGW). right; right; right. unfold Sh in *. unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in *. lia.
Qed.
Lemma DZ_QFP : ltac2:(tb__ "0|0|
S4fS4fS0S1dS61S50R3A1S50R2A1A3Sb2R4Z18R2A3S46R4R3A2F_;F_;Fz;FA0';FA;").
Proof.
  intros A A0' z EG HZ. unfold DZ in HZ. cbv zeta in HZ. rewrite EG in HZ. unfold QFP. destruct HZ as [H|[H|[H|H]]].
  - right; left. lia.
  - right; right; left. exists 24. split; [lia|]. left. exact H.
  - right; right; left. exists 24. split; [lia|]. right; left. exact H.
  - right; right; left. exists 24. split; [lia|]. right; right. exact H.
Qed.
Lemma view_range : ltac2:(tb__ "0|2|
S3fQ40A1S2aS3fQ8A1M0A1M1F_;S0S20S1dG1S63S3eR2R1A3S2eG0A1A3A1S1eS33Z0R2A2S35R2S36Z2Z40A2A2A2F_;Fz;Fm;").
Proof.
  intros m z H. unfold view in H. destruct ((0 <=? z) && (z <? 2 ^ 64))%bool eqn:E; [|exfalso; exact (H eq_refl)].
  apply andb_true_iff in E as (E1 & E2). apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.

Lemma AInvQ_parts' : ltac2:(tb__ "0|2|
S4fS6S25S3fQ40A1A1S71S77R4R3R2R1A4S1eSbeS50R5A1M0A1S1eSbfR5A1S1eS47R5A1S1eS0S1eS33Z1R1A2S33R1Z1eA2A2S1eS33Z0S5bS44R7R2A2A1M1A2S33G1SaeA2A2F_;Fc;Sc0S66SbdG0A1S63S3eSaR4A1A2A2R5A2A2A2A2A2F_;Fmd;Ftpx;Fr;FAx;").
Proof.
  intros Ax r tpx md (HG & _ & HF & HRest & _ & HI3 & _). cbn zeta in HRest, HF. destruct HRest as (R1 & _ & R3 & R4 & (R5 & _) & _).
  split; [exact HG|]. split; [exact HI3|]. split; [exact R5|]. split; [|exact R4].
  intros c Hc. destruct R3 as (_ & _ & _ & P4). pose proof (P4 c Hc) as HC. unfold class_repr in HC. cbn zeta in HC.
  destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _). unfold SegQ_wf2.cls_of, kUserMapSize in *. lia.
Qed.

Lemma qcf_exit_core : ltac2:(tb__ "0|8|
S24S4fS0S0S0S26S25S51A1M0G0S6S25S3fQ40A1A1M1S25S72A1M2S92S71S6G1S1dG0S58ReA1S28S51A1A3S1dS24S53RfA1S29A3S79VA0;R10A2S1dG0S57R11A1S27S51S5dR10S28S23S0S0A2A1M3RfA3S2cS51RcRbA3A3A3S1dS0S37S2dS0S54S44R12Z18M4A2A1A2A1Z2A3S1dS24S7fG4S44R13G4A2A2R14A3S85R14RdA2S7bS3eReRdS67R16A1S22G2S93RcS94RbRaA2A4A5S78S76VKc;A1M5VA0;Vrho0;R16R15R13R12G3R11R10RfReRdRbAeS6SbaS96R12S6eReR11RfA3S68R1aA1S6aR1aA1S4cS69R1aA1A1S4cS67R1aA1A1S4cS6bR1aA1A1R2RdA9S7aS3eS9fS98R1aVKc;G4A3S4aS49R13S68R1bA1M6S6eRfR12R10A3A3S6aR1bA1M7A2R12ReRdA5Sa2G7S69R1bA1S6bR1bA1S67R1bA1G6A5R3RdR2A6S1fS6S6S1eS7aS3eS78G5VA0;Vrho0;S80R1cG4A2R1bR19R18G3R17R16AaS6cR1dA1R1RfR4A6S95ScS4cS67R1dA1A1A1R15R1A3A2Lrho5;A2F_;F_;Fw';Frho';F_;F_;F_;F_;F_;F_;F_;F_;F_;FtpL;FrhoL;Fmd;Fms;Ftr;Ftp;Frho;Frest;Ftmp';Fnd;Fn0;Fs;Fa;FA;Fg;").
Proof.
  intros g A a s n0 nd tmp' rest rho tp tr ms md rhoL tpL HTH HCI HQP HGL HFULL HGR HENV Hsm0 HJ0 rho' w' HLK [Hsm' HJ'].
  pose proof HENV as (EC & E201 & E208 & E221 & E222 & E223 & E224 & E225 & E231).
  pose proof HJ0 as (HK & HCB & HRMM & HFRM).
  destruct (XF0 g) as (XP & XC & XT & NXP & NXC).
  assert (EG : aa_geom A = aa_geom A0) by (destruct HQP as (ESB & _); unfold same_but_qcs in ESB; rewrite ESB; reflexivity).
  pose proof (smatch_facts_hold _ _ _ _ (proj1 Hsm0)) as HFa.
  assert (HFp : Forall (holds rho) (pre_facts DEPTH_R)).
  { apply Forall_forall. intros f Hf. pose proof (proj1 (forallb_forall _ _) (C1_pre g) f Hf) as X. apply existsb_exists in X as (f' & Hf' & E). apply sprop_eqb_sound in E. subst f'.
    exact (proj1 (Forall_forall _ _) HFa f Hf'). }
  pose proof (fr_all Kc A rho tp tr md HKc HK HCI HFp EC E201 E208 g) as FRA.
  destruct (frame_view A (C1 g) _ (RF g) rho tp tr ms md Hsm0 (C1_objs g) FRA) as (_ & _ & _ & FR4). set (r3 := rho_absorb rho (RF g) (vms md tp ms)) in *.
  destruct (entails_frA_sound segsA (C1 g) (PreD g) (sF g) (RF g) rho tp tr ms md (HeF g) Hsm0) as (_ & _ & _ & HwfR & HinR).
  destruct w' as [tr2 [ms2 md2]]. cbn [w_tr w_cfg cfg_model fst snd] in HJ'.
  pose proof HJ' as HJc. unfold J_ofPA in HJ'. destruct HJ' as (HK3 & HRM & HDEF & HRL3).
  pose proof HLK as (Hag' & Hrm' & HagL' & Hlink').
  assert (HF4 : Forall (holds rho') (ss_facts (ax_S (C1 g)))).
  { apply Forall_forall. intros f Hf. exact (proj1 (holds_agree_vals _ rho rho' f Hag' (proj1 (forallb_forall _ _) (FBC1 g) f Hf)) (proj1 (Forall_forall _ _) HFa f Hf)). }
  assert (HT40 : SPA segsA (J_ofPA (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS.JLD A Kc 24) (rho_sub r3 (sF g)) tp rhoL tpL) (T1f g) rho' tpL (tr2, mkCfg ms2 md2)).
  { rewrite <- (T1f_eq g). apply (SPA_refacts segsA); [exact (conj Hsm' HJc) | exact (FBT1 g) | intros _; exact HF4]. }
  assert (RNG : forall o, In o (RF g) -> obj_range rho' o = obj_range rho o).
  { intros o Ho. apply (obj_range_agree_vals (ss_next (ax_S (C1 g)))); [exact Hag' | exact (proj1 (forallb_forall _ _) HwfR o Ho)]. }
  set (rho5 := rho_absorb rho' (RF g) (ms_with_mem ms2 (rm rho))).
  assert (RM5 : forall x, rm rho5 x = if in_ranges_dec rho' (RF g) x then rm rho x else rm rhoL x).
  { intros x. unfold rho5, rho_absorb, ms_with_mem. cbn [rm ms_mem]. rewrite Hrm'. reflexivity. }
  assert (IRE : forall x, in_ranges rho' (RF g) x <-> in_ranges rho (RF g) x).
  { intros x. split; intros (o & Ho & Hox); exists o; [rewrite <- (RNG o Ho) | rewrite (RNG o Ho)]; exact (conj Ho Hox). }
  assert (KEPT : forall x, in_ranges rho (RF g) x -> rm rhoL x = rm r3 x).
  { intros x Hin. apply (HRM x). intros HZ. exact (floc_out Kc A rho tp tr md HKc HK _ (proj1 (FR4 x Hin)) (dzone_coarse Kc A rho tp tr md HKc HK _ HZ HCI)). }
  assert (KEY : forall x : word, ~ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS.drain_zone (aa_geom A) 24 (SegQ_wf2.cls_of A 24) (bv_unsigned x) -> rm rho5 x = rm rho x).
  { intros x Hx. rewrite RM5. destruct (in_ranges_dec rho' (RF g) x) as [Hi|Hn]; [reflexivity|]. rewrite (HRM x Hx). cbn [rm rho_sub]. apply rm_absorb_out. intros Hi. exact (Hn (proj2 (IRE x) Hi)). }
  assert (DEF5 : forall x : word, SHADOW_BAND_LO <= bv_unsigned x < SHADOW_BAND_HI -> rm rho x <> None -> rm rho5 x <> None).
  { intros x HBx Hd. rewrite RM5. destruct (in_ranges_dec rho' (RF g) x) as [Hi|Hn]; [exact Hd|].
    apply (HDEF x HBx). cbn [rm rho_sub]. unfold r3. rewrite (rm_absorb_out _ _ _ _ (fun Hi => Hn (proj2 (IRE x) Hi))). exact Hd. }

  set (A1 := drainA A 24).
  pose proof HK3 as (HAQ3 & HKc3 & _).
  destruct (AInvQ_parts' A1 rhoL tpL md2 HAQ3) as (HG3 & HI33 & HQP3 & HAU3 & HSR3).
  assert (QWT : forall z, QW A z -> z < topG (aa_geom A)).
  { intros z HQ. exact (QRD_lt_top A1 HG3 HI33 HQP3 HAU3 _ HSR3 z (QRD_QFP A1 z (or_introl HQ))). }
  assert (V5IN : forall z, 0 <= z < 2 ^ 64 -> in_ranges rho' (RF g) (Z_to_bv 64 z) -> view segsA (rm rho5) z = view segsA (rm rho) z).
  { intros z Hr Hi. apply view_agree. intros _. rewrite RM5. destruct (in_ranges_dec rho' (RF g) (Z_to_bv 64 z)) as [|Hn]; [reflexivity | exfalso; exact (Hn Hi)]. }
  assert (V5OUT : forall z, ~ in_ranges rho' (RF g) (Z_to_bv 64 z) -> view segsA (rm rho5) z = view segsA (rm rhoL) z).
  { intros z Hn. apply view_agree. intros _. rewrite RM5. destruct (in_ranges_dec rho' (RF g) (Z_to_bv 64 z)) as [Hi|]; [exfalso; exact (Hn Hi) | reflexivity]. }
  assert (VL3 : forall z, 0 <= z < 2 ^ 64 -> in_ranges rho (RF g) (Z_to_bv 64 z) -> view segsA (rm rhoL) z = view segsA (rm r3) z).
  { intros z Hr Hi. apply view_agree. intros _. exact (KEPT _ Hi). }
  set (r5 := set_rm rhoL (rm rho5)).
  assert (HK5' : K0 Kc A1 r5 tpL tr2 md2).
  { apply (K0_blind Kc A1 rhoL r5 tpL tr2 md2); [intros i; reflexivity | intros l; reflexivity | | | exact HK3].
    - intros z Hz NQ. unfold r5. cbn [rm set_rm]. destruct (Z_le_dec 0 z) as [Z0|Z0]; [destruct (Z_lt_dec z (2 ^ 64)) as [Z1|Z1]|].
      2, 3: unfold view; replace ((0 <=? z) && (z <? 2 ^ 64))%bool with false; [reflexivity | symmetry; apply andb_false_iff; first [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia]].
      destruct (in_ranges_dec rho' (RF g) (Z_to_bv 64 z)) as [Hi|Hn]; [|exact (V5OUT z Hn)].
      pose proof (proj1 (IRE _) Hi) as Hi'. rewrite (V5IN z ltac:(lia) Hi). rewrite (VL3 z ltac:(lia) Hi').
      destruct (FR4 _ Hi') as (_ & ALT). rewrite u64_lit in ALT by lia. destruct ALT as [ALT|[ALT|ALT]].
      + exfalso. change (aa_geom A1) with (aa_geom A) in Hz. lia.
      + exfalso. exact (NQ (proj1 ALT)).
      + symmetry. exact ALT.
    - intros z HQ Hd. unfold r5. cbn [rm set_rm]. pose proof (view_range _ _ Hd) as Hr.
      destruct (in_ranges_dec rho' (RF g) (Z_to_bv 64 z)) as [Hi|Hn]; [|rewrite (V5OUT z Hn); exact Hd].
      pose proof (proj1 (IRE _) Hi) as Hi'. rewrite (V5IN z Hr Hi). rewrite (VL3 z Hr Hi') in Hd.
      destruct (FR4 _ Hi') as (_ & ALT). rewrite u64_lit in ALT by lia. destruct ALT as [ALT|[ALT|ALT]].
      + exfalso. pose proof (QWT z HQ). lia.
      + exact (proj2 ALT).
      + rewrite <- ALT. exact Hd. }
  destruct HK5' as (HA5 & HKc5 & _).
  pose proof HK as (_ & _ & Htp & Htop & HRG).
  assert (RW5 : forall i, (i < 260)%positive -> rw rho5 i = rw rho i).
  { intros i Hi. unfold rho5. cbn [rw rho_absorb]. symmetry. apply (proj1 Hag'). rewrite NXC. exact Hi. }
  assert (HK5 : K0 Kc A1 rho5 tpL tr2 md2).
  { split; [exact HA5|]. split; [exact HKc5|]. split; [|split].
    - unfold tp_ok in *. rewrite (RW5 24%positive eq_refl). exact Htp.
    - unfold top_high, V_DEPTH in *. rewrite (RW5 10%positive eq_refl), (RW5 15%positive eq_refl). exact Htop.
    - unfold rigidQ in *. rewrite (RW5 151%positive eq_refl), (RW5 152%positive eq_refl), (RW5 155%positive eq_refl), (RW5 156%positive eq_refl). exact HRG. }

  pose proof (K0_laws Kc HKc) as HL.
  destruct (kq_facts segsA (K0 Kc) HL A rho tp _ _ HK) as [HG _ _ _ _ HLEN HCLS _ _ _ _ _ _].
  destruct (kq_facts segsA (K0 Kc) HL A1 rhoL tpL _ _ HK3) as [_ _ _ _ _ _ HCLS3 _ _ _ _ _ _].
  pose proof (HCLS HCI 24 ltac:(lia)) as CV. pose proof (cv_fa_bounds _ _ _ _ _ CV) as (FB1 & FB2 & FB3).
  pose proof (HCLS3 HCI 24 ltac:(lia)) as CV3. pose proof (cv_fa_bounds _ _ _ _ _ CV3) as (_ & FC2 & FC3).
  unfold A1 in FC2, FC3. rewrite (drainA_cls A ltac:(rewrite HLEN; lia)) in FC2, FC3. unfold drain_cs in FC2, FC3. cbn [cs_free_array cs_mapped_free_array] in FC2, FC3.
  rewrite length_app, length_skipn in FC2. unfold drain_keep in FC2. change (Z.to_nat (kchunks 24)) with 1%nat in FC2.
  destruct (geo_nums Kc A rho tp tr md HKc HK) as (S1 & _ & _). cbv zeta in S1. unfold HIGH_SHADOW_END in S1.
  assert (DZI : forall z, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS.drain_zone (aa_geom A) 24 (SegQ_wf2.cls_of A 24) z -> DZ A 24 z).
  { intros z HZ. apply (dzone_DZ A z); [lia | lia | | | exact HZ].
    - destruct (drain_grows 24 (SegQ_wf2.cls_of A 24)); lia.
    - intros EGW. rewrite EGW in FC3. exact FC3. }
  assert (VOUT : forall z, ~ DZ A 24 z -> view segsA (rm rho5) z = view segsA (rm rho) z).
  { intros z Hz. apply view_agree. intros Hr. apply KEY. rewrite u64_lit by exact Hr. intros HZ. exact (Hz (DZI z HZ)). }
  assert (VBAND : forall z, SHADOW_BAND_LO <= z < SHADOW_BAND_HI -> view segsA (rm rho) z <> None -> view segsA (rm rho5) z <> None).
  { intros z HB Hd. pose proof (view_range _ _ Hd) as Hr. rewrite view_in in Hd |- * by exact Hr.
    destruct (rd_of segsA (rm rho) (Z_to_bv 64 z)) as [x|] eqn:E; [|exfalso; exact (Hd eq_refl)].
    pose proof (rd_off_image (rm rho) z x ltac:(unfold SHADOW_BAND_LO, LOW_SHADOW_BEG in HB; lia) E) as E'.
    pose proof (DEF5 (Z_to_bv 64 z) ltac:(rewrite u64_lit by exact Hr; exact HB) ltac:(rewrite E'; discriminate)) as D5.
    unfold rd_of. destruct (rm rho5 (Z_to_bv 64 z)); [discriminate | exfalso; exact (D5 eq_refl)]. }
  destruct (CR_drain (K0 Kc) HL (K0_secband Kc) A a s [] tmp' rest 24 HTH HCI HGL ltac:(lia) rho tp tr md (view segsA (rm rho)) (view segsA (rm rho5)) n0 nd HK VOUT VBAND HCB HRMM) as (HCB5 & HRM5).
  destruct HFRM as ((F1 & F1') & F2 & F3 & F4).
  assert (HFRM5 : FRM A0 rho0 rho5).
  { split; [split|split; [|split]].
    - intros i Hi. rewrite (F1 i Hi). symmetry. apply RW5. unfold NPRE in Hi. lia.
    - intros l. rewrite (F1' l). unfold rho5. cbn [rl rho_absorb]. exact (proj2 Hag' l).
    - intros x Hx. rewrite KEY; [exact (F2 x Hx)|]. intros HZ. apply Hx. apply QRD_QFP. exact (DZ_QFP A A0 _ EG (DZI _ HZ)).
    - intros z Hz. rewrite VOUT; [exact (F3 z Hz)|]. intros HZ. exact (Hz (DZ_QFP A A0 _ EG HZ)).
    - intros x HBx Hd. exact (DEF5 x HBx (F4 x HBx Hd)). }
  exists rho5. split.
  - pose proof (proj1 (proj1 HT40)) as HsmT. pose proof (smatch_facts_hold _ _ _ _ HsmT) as HfT.
    unfold rho5. apply (SPA_absorb_any segsA (J_ofPA (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS.JLD A Kc 24) (rho_sub r3 (sF g)) tp rhoL tpL)); [exact XT | | exact HT40 | ].
    + intros o x Ho Hx. exact (coveredb_sound _ _ _ rho' o x HfT (RF_cov g) Ho Hx).
    + cbn [w_tr w_cfg cfg_model fst snd]. fold rho5. split; [exact HK5|]. split; [exact HCB5|]. split; [exact HRM5 | exact HFRM5].
  - split; [intros i Hi; symmetry; apply RW5; rewrite NXC in Hi; exact Hi | intros l; unfold rho5; cbn [rl rho_absorb]; exact (proj2 Hag' l)].
Qed.
End CallF.

Section CallT.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variables (A0 : AA) (rho0 : valuation).
Context {Q : assn} (X : trk Q).

Hypothesis HDC : ltac2:(tb__ "0|3|
S24S4fS6S25S3fQ40A1A1S1dS24R4S29A3S33S5aR4A1Sa3A2F_;Sb4VQ;VX;S7aS3eS99Z1R5R4VKc;Z18M0A5S69R5A1M1R3R2A5Sa0S3eScS4cG1A1A1R3R2S27S23S4eS9eA2M2S22S4eS9eS6bR5A1S98R4VKc;G0A3A4S28G2A1A3A5A4F_;Ftp1;Frho1;FA;Fg;").

Lemma qcf_call : ltac2:(tb__ "0|5|
S24S4fS0S0S0S26S25S51A1M0G0S6S25S3fQ40A1A1M1S1dG0S58R9A1S28S51A1A3S1dS24S53RaA1S29A3S79VA0;RbA2S1dG0S57RcA1S27S51S5dRbS28S23S0S0A2A1M2RaA3S2cS51R7R6A3A3A3S1dS0S37S2dS0S54S44RdZ18M3A2A1A2A1Z2A3S1dS24S7fG3S44ReG3A2A2RfA3S1dS24R10S29A3S33S5aR10A1Sa3A2F_;S85R10R9A2S6G1S95ScS4cS67R14A1A1A1RcR2A3Sb3VQ;VX;S7aS3eS78S76VKc;A1M4VA0;Vrho0;S80R14G3A2R13R11R10G2RfReAaS6cR15A1R3R2A5A3F_;FtpL;Frho5;Sb3VQ;VX;S7aS3eS78G4VA0;Vrho0;R12R11RfReG2RdRcAaS67R13A1RbRaA5A3F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp;Frho;Frest;Ftmp';Fnd;Fn0;Fs;Fa;FA;Fg;").
Proof.
  intros g A a s n0 nd tmp' rest rho tp HTH HCI HQP HGL HFULL HGR HB HENV HC.
  apply (tr_callP X (JRI (K0 Kc) A0 rho0 A a n0 nd [] tmp' rest) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS.JD 1 g A Kc 24) (C1 g) (PreD g) (sF g) (RF g) [(PostD g, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS.JLD A Kc 24)] rho tp (HeF g) (HchkF g)).
  - intros rho1 tp1. exact (HDC g A rho1 tp1 HB).
  - intros tr ms md Hsm HJ. exact (qcf_JP Kc HKc A0 rho0 g A a n0 nd tmp' rest rho tp tr ms md HCI HFULL HGR HENV Hsm HJ).
  - intros L JL tr ms md rhoL tpL tr' ms' md' Hin Hsm HJ Hag HsmL HJL. destruct Hin as [E|[]]. injection E as <- <-. split.
    + exact (qcf_post_ok Kc HKc A0 rho0 g A a n0 nd tmp' rest rho tp tr ms md rhoL tpL tr' md' HCI HFULL HGR HENV Hsm HJ Hag HJL).
    + intros rho' HLK.
      apply (tr_glue X _ (JRI (K0 Kc) A0 rho0 (drainA A 24) a n0 nd [] tmp' rest) (T1f g) tpL (fun r => agree_vals (ss_next (ax_S (C1 g))) rho r)); [|intros r Hr; exact (HC r tpL Hr)].
      intros w' Hw'. exact (qcf_exit_core Kc HKc A0 rho0 g A a s n0 nd tmp' rest rho tp tr ms md rhoL tpL HTH HCI HQP HGL HFULL HGR HENV Hsm HJ rho' w' HLK Hw').
Qed.
End CallT.
End SegQCF_call.

(* [comment removed for export] *)
Module SegQ3M_sum.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "qbatch"; "AA"; "aa_q_thread"; "aa_q_global"; "aa_cache_inited"; "budget_bound"; "@Corelib.Init.Datatypes"; "list"; "nil"; "app"; "bool"; "true"; "nat"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "True"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post"; "PostsQ3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr"; "JOK"; "trk"; "TR"; "trC"; "trS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "holds"; "sprop"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "qsize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQ3D_qcs"; "QC_full_step"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jg.SegQ3D_qis"; "QI_full_step"; "QI_sec_step"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ls.SegQ3M_sum"; "q3_arms3"; "q3_arms3E"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "QW"; "qbounded"; "qzone"; "sec_foot"; "set_q"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_exit"; "F_T0x"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv"; "JRD"; "JRI"; "QP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_loop"; "QC_step"; "QI_step"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_sum"; "PM_step"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lq.SegQ3D_top"; "q3_arms2"; "q3_arms2E"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue"; "GI"; "JRM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop"; "HVX"; "JRX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel"; "JRQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states"; "Xg"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SysCallA SummaryA GlueA.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_sum OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lc.SegQ3_sum OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lm.SegQ3D_rec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQ3D_qcs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jg.SegQ3D_qis OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvQ9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lq.SegQ3D_top OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3M_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3M_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma qzone_regroup : ltac2:(tb__ "0|2|
S1S6S0A1M0G0S12SeG0S2R4A1S7S0A1M1A3S43S3R5A1R4R3A3S32S34R6G1S8S0R5R4A3A3R3A2S32R7R4A2F_;F_;F_;Fz;Fglob;FE;FA1;").
Proof.
  intros A1 E glob z HTH (P1 & P2 & _) H. unfold qzone, qall in *. cbn [aa_q_thread aa_q_global set_q app] in H. rewrite HTH. cbn [app].
  apply List.Exists_exists in H as (b & Hb & Hz). destruct Hz as [Hz|Hz].
  - assert (Ha : In (qb_addr b) (map qb_addr (aa_q_global A1))) by (eapply Permutation_in; [symmetry; exact P1 | apply in_map; exact Hb]).
    apply in_map_iff in Ha as (b0 & E0 & Hb0). apply List.Exists_exists. exists b0. split; [exact Hb0|]. left. rewrite E0. exact Hz.
  - apply List.Exists_exists in Hz as (it & Hit & Hc).
    assert (Hi : In it (qitems (aa_q_global A1))) by (eapply Permutation_in; [symmetry; exact P2 | unfold qitems; apply in_flat_map; exists b; split; assumption]).
    unfold qitems in Hi. apply in_flat_map in Hi as (b0 & Hb0 & Hit0). apply List.Exists_exists. exists b0. split; [exact Hb0|]. right. apply List.Exists_exists. exists it. split; assumption.
Qed.

Section MSum.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.
Hypothesis HREG : KQ_regroup K.
Variables (A : AA) (rho : valuation) (tp : list word).
Hypothesis HCI : aa_cache_inited A = true.
Hypothesis HBND : qbounded A.
Context {Q : assn} (X : trk Q).
Hypothesis HQ : ltac2:(tb__ "0|0|
S20S13SdS14Vrho;Vtp;S15VK;VA;A2R1A6VQ;R2A1F_;Fw;").
Hypothesis HJQ : ltac2:(tb__ "0|1|
S1S6S0A1M0G0S1bVQ;VX;S47VK;VA;Vrho;R3R2R1A6A3Frest;Fpre;FA1;").
Hypothesis HJD : ltac2:(tb__ "0|1|
S1S6S0A1M0G0S1bVQ;VX;S3bVK;VA;Vrho;R3R2R1A6A3Frest;Ftmp;FA1;").
Hypothesis HJI : ltac2:(tb__ "0|1|
S1S12S12SbS6ScS12S12A2A1S6S0A1M0G0S1bVQ;VX;S3cVK;VA;Vrho;R7R6R5R4R3R2R1AaA3Frest;Ftmp;Fits;Fnd;Fn0;Fa;FA1;").
Hypothesis HJM : ltac2:(tb__ "0|1|
S1S6S0A1M0G0S0S0SbS1bVQ;VX;S44VK;VA;Vrho;R6R5R4R3R2R1A9A3Fj;Fn;Fc;Fglob;FE;FA1;").
Let TPI : list word -> Prop := fun _ => True.
Let all : list qbatch := ltac2:(tb__ "0|0|
S8S0S3VA;A1S2VA;A1A3").
Hypothesis HQI : ltac2:(tb__ "0|0|
S6S0A1S3fVK;VA;Vrho;VQ;VX;R1VTPI;A7Frest;").
Hypothesis HQC : ltac2:(tb__ "0|0|
S6S0A1S3eVK;VA;Vrho;VQ;VX;R1VTPI;A7Frest;").

Lemma cont_gen : ltac2:(tb__ "0|2|
S1SeS6S0A1M0S2R1A1S7S0A1M1A3SeS9S4R2A1SaA3S12S30R4R1A2S30VA;R2A2F_;Fz;S3dVA;R4A2S25S29S3R5A1A1S26Z2Z3eA2A2S12S33R7R1A2S33VA;R2A2F_;Fz;S36S23S22Vrho;A1S3aA3G0G0S21S10SeG0R3G1A3A1SeG0S3RcA1S8S0R4R3A3A3S24S29R4A1S39A2S45R4R6A2S1dVQ;VX;S18SdS46VK;VA;Vrho;RfR7R6A6S48R5Vtp;A5A3F_;F_;F_;F_;Frho3;Frest';Ftmp;F_;F_;F_;F_;F_;F_;F_;FA1;").
Proof.
  intros A1 HTH1 HCI1 HQW1 HQP1 HSZ1 HSF1 HF0 tmp rest' rho3 NEt HG HS HV.
  apply (tr_pure X _ (0 <= qsize rest')).
  { intros [tr [ms md]] Hw. destruct (proj2 Hw) as (HK & (HBM & _) & _). cbn [w_tr w_cfg cfg_model fst snd] in HK, HBM.
    pose proof (benv_of_K K HL A1 HCI1 rho3 tp tr md HK) as BE. pose proof (proj1 (be_qp _ _ BE)) as HBP. rewrite (qall_A1 A1 HTH1) in HBP.
    rewrite HG in HBP. apply Forall_app in HBP as [_ P2]. apply Forall_app in HBM as [_ M2].
    pose proof (qsize_ge A1 _ rest' P2 M2) as Q2. unfold kQuarantineBatchSize in Q2. lia. }
  intros HR0.
  apply (dorecycle_xg K HL A rho X HJD HJI rest' TPI (HQI rest') (HQC rest')); [| exact I | exact NEt | | | exact HV].
  - intros A' rho4 tp4 HTP (I1 & I2 & I3 & I4 & I5 & I6) E208.
    eapply (tr_conseq X); [|apply (tr_done X); exact HQ]. intros w Hw.
    apply (exit_R K HL A rho A' rest' rho4 tp tp4 w I1 I2 I3 I4 I5); [| exact E208 | exact HF0 | exact Hw].
    unfold kQuarantineMin, kQuarantineMax in *. lia.
  - split; [exact HTH1|]. split; [exact HCI1|]. split; [exact HQW1|]. split; [exact HQP1|]. split; [exact HG | exact HSF1].
  - rewrite HG, qsize_app in HSZ1. lia.
Qed.

Theorem pm_step_of : ltac2:(tb__ "0|0|
S40VK;VA;Vrho;Vtp;VQ;VX;A6").
Proof.
  intros HF0 HGT rho' HVp. fold all in HGT, HVp.
  assert (HSZ : qsize all < 2 ^ 50).
  { unfold all. rewrite qsize_app. destruct HBND as [B1 B2]. unfold kQuarantineMax in B2. lia. }
  assert (QWT : forall z, QW (A1T A) z -> QW A z).
  { intros z [H|H]; [left | right; exact H]. unfold A1T in H.
    apply (proj1 (qzone_perm A [] (aa_q_global A ++ aa_q_thread A) z ltac:(unfold qall; cbn [app]; apply Permutation_app_comm))). exact H. }

  assert (REG : forall E glob, GI all E glob ->
            let A1' := set_q (A1T A) [] (E ++ glob) in
            (forall z, QW A1' z -> QW A z) /\ QP A A1' /\ qsize (aa_q_global A1') < 2 ^ 62 /\ (forall z, sec_foot A1' z -> sec_foot A z)).
  { intros E glob HGI A1'. split; [|split; [|split]].
    - intros z [H|H]; [|apply QWT; right; exact H]. apply QWT. left. exact (qzone_regroup (A1T A) E glob z eq_refl HGI H).
    - exact (QP_refl_q A [] (E ++ glob)).
    - cbn [aa_q_global set_q A1']. destruct HGI as (_ & _ & _ & _ & QS). rewrite QS. lia.
    - intros z. apply sec_foot_mono; [reflexivity | intros y Hy; exact Hy |]. unfold A1', A1T, qall. cbn [aa_q_thread aa_q_global set_q app].
      destruct HGI as (_ & P2 & _). intros y Hy. apply (Permutation_in y (Permutation_sym P2)) in Hy. fold all in Hy. unfold all in Hy. rewrite qitems_app in *. apply in_app_or in Hy. apply in_or_app. tauto. }
  apply (merge_pm K HL A rho (A1T A) eq_refl HCI QWT HSZ HREG X tp (HJM (A1T A)) (HJQ (A1T A) [] _) HGT); [| | | exact HVp].
  - intros glob r HGI NG HH. destruct (REG [] glob HGI) as (R1 & R2 & R3 & R4). cbv zeta in R1, R2, R3, R4.
    destruct glob as [|cur rest']; [congruence|]. destruct (head0_vals cur rest' _ r HH) as [W1 W2].
    eapply (tr_conseq X); [intros w Hw; exact (proj1 (head0_carve K HL A rho (set_q (A1T A) [] ([] ++ cur :: rest')) eq_refl HCI cur rest' _ r tp w eq_refl Hw HH))|].
    exact (deq_loop_0 K HL A rho (set_q (A1T A) [] ([] ++ cur :: rest')) eq_refl HCI R1 X (HJQ _) tp R3
             (cont_gen (set_q (A1T A) [] ([] ++ cur :: rest')) eq_refl HCI R1 R2 R3 R4 HF0) cur rest' _ eq_refl W1 W2).
  - intros E glob r HGI NE NG HH HC HT. destruct (REG E glob HGI) as (R1 & R2 & R3 & R4). cbv zeta in R1, R2, R3, R4.
    exact (deq_loop_k K HL A rho (set_q (A1T A) [] (E ++ glob)) eq_refl HCI R1 X (HJQ _) tp R3
             (cont_gen (set_q (A1T A) [] (E ++ glob)) eq_refl HCI R1 R2 R3 R4 HF0) glob E r NE NG eq_refl HH HC HT).
  - intros E glob r HGI NE HMIN HXx. destruct (REG E glob HGI) as (R1 & R2 & R3 & R4). cbv zeta in R1, R2, R3, R4.
    exact (cont_gen (set_q (A1T A) [] (E ++ glob)) eq_refl HCI R1 R2 R3 R4 HF0 E glob r NE eq_refl HMIN HXx).
Qed.
End MSum.

Definition q3_arms3 (ok : world -> Prop) (Kc : KcA) : Prop := ltac2:(tb__ "0|6|
S1S21S6S35Q40A1A1M0S10SeS6S0A1M1S2R3A1S7S0A1A3A1SeS9S4R4A1SaA3S31R5A1S24S5R6A1S28A2S1fVok;S13SdS14R6R5S15S2aVKc;A1M2R7A2A5M3A2S1cG3A1SfG1S2dG2R9R8S13SdS14R8R7S15G2R9A2A5M4R2R1G0S11L_;M5A7Frest;SfG1S2cG2R9R8G4R2R1G5A7Frest;G1S2bG2R9R8G4R2R1G5A7Frest;A2A2TX;F_;F_;F_;F_;Ftp;Frho;FA;").
Definition q3_arms3E (Kc : KcA) : Prop := ltac2:(tb__ "0|6|
S1S21S6S35Q40A1A1M0S10SeS6S0A1M1S2R3A1S7S0A1A3A1SeS9S4R4A1SaA3S31R5A1S24S5R6A1S28A2S1eS13SdS14R6R5S15S2aVKc;A1M2R7A2A5M3A1S1cG3A1SfG1S2dG2R9R8S13SdS14R8R7S15G2R9A2A5M4R2R1G0S11L_;M5A7Frest;SfG1S2cG2R9R8G4R2R1G5A7Frest;G1S2bG2R9R8G4R2R1G5A7Frest;A2A2TX;F_;F_;F_;F_;Ftp;Frho;FA;").

Theorem q3_arms2_of_arms3 : ltac2:(tb__ "0|0|
S20OF_;S19S1aR1A1S17SdR3S16R2A1A3S27SdR4S16R3A1A3S2eR5R4A2S41R6R5A2F_;F_;F_;F_;FKc;Fok;").
Proof.
  intros ok Kc HKc Hok Hokp HA A rho tp HT HCI HQB HBD. destruct (HA A rho tp HT HCI HQB HBD) as (HQIS & HQIF & HQCF). cbv zeta in HQIS, HQIF, HQCF |- *.
  pose proof (K0_laws Kc HKc) as HL. pose proof (fun A0 => K0_ok_frame ok Kc A0 Hok) as HOKK.
  set (X := trS ok (LQPA segsA NPRE rho tp (PostsQ3 (K0 Kc) A))) in *.
  assert (HJQ : forall A1 pre rest, JOK X (JRQ (K0 Kc) A rho A1 pre rest)) by (intros; split; [apply JRQ_okf; exact HOKK | split; [apply (okp_via ok Kc _ Hokp); intros r0 t0 tr0 md0 HJ0; exact (proj1 (proj2 (proj1 HJ0))) | apply JRQ_stable; exact HL]]).
  assert (HJD : forall A1 tmp rest, JOK X (JRD (K0 Kc) A rho A1 tmp rest)) by (intros; split; [apply JRD_okf; exact HOKK | split; [apply (okp_via ok Kc _ Hokp); intros r0 t0 tr0 md0 HJ0; exact (proj1 (proj2 (proj1 HJ0))) | apply JRD_stable; exact HL]]).
  assert (HJI : forall A1 a n0 nd its tmp rest, JOK X (JRI (K0 Kc) A rho A1 a n0 nd its tmp rest)) by (intros; split; [apply JRI_okf; exact HOKK | split; [apply (okp_via ok Kc _ Hokp); intros r0 t0 tr0 md0 HJ0; exact (proj1 (proj2 (proj1 HJ0))) | apply JRI_stable; exact HL]]).
  assert (HJM : forall A1 E glob c n j, JOK X (JRM (K0 Kc) A rho A1 E glob c n j)) by (intros; split; [apply JRM_okf; exact HOKK | split; [apply (okp_via ok Kc _ Hokp); intros r0 t0 tr0 md0 HJ0; exact (proj1 (proj2 (proj1 HJ0))) | apply JRM_stable; exact HL]]).
  split; [exact HQIS|]. split; [exact HQIF|]. split; [exact HQCF|].
  apply (pm_step_of (K0 Kc) HL (K0_regroup Kc) A rho tp HCI HQB X (fun w Hw => Hw) HJQ HJD HJI HJM).
  - intros rest. exact (QI_step_of_arms (K0 Kc) HL (K0_secband Kc) A rho X HJI rest _ (HQIS rest) (HQIF rest)).
  - intros rest. exact (QC_step_of_full (K0 Kc) HL A rho X HJD HJI rest _ (HQCF rest)).
Qed.
Theorem q3_arms2E_of_arms3 : ltac2:(tb__ "0|0|
S19S1aR1A1S2fR2A1S42R3A1F_;F_;FKc;").
Proof.
  intros Kc HKc HA A rho tp HT HCI HQB HBD. destruct (HA A rho tp HT HCI HQB HBD) as (HQIS & HQIF & HQCF). cbv zeta in HQIS, HQIF, HQCF |- *.
  pose proof (K0_laws Kc HKc) as HL.
  set (X := trC (LQPA segsA NPRE rho tp (PostsQ3 (K0 Kc) A))) in *.
  assert (HJQ : forall A1 pre rest, JOK X (JRQ (K0 Kc) A rho A1 pre rest)) by (intros; apply JRQ_stable; exact HL).
  assert (HJD : forall A1 tmp rest, JOK X (JRD (K0 Kc) A rho A1 tmp rest)) by (intros; apply JRD_stable; exact HL).
  assert (HJI : forall A1 a n0 nd its tmp rest, JOK X (JRI (K0 Kc) A rho A1 a n0 nd its tmp rest)) by (intros; apply JRI_stable; exact HL).
  assert (HJM : forall A1 E glob c n j, JOK X (JRM (K0 Kc) A rho A1 E glob c n j)) by (intros; apply JRM_stable; exact HL).
  split; [exact HQIS|]. split; [exact HQIF|]. split; [exact HQCF|].
  apply (pm_step_of (K0 Kc) HL (K0_regroup Kc) A rho tp HCI HQB X (fun w Hw => Hw) HJQ HJD HJI HJM).
  - intros rest. exact (QI_step_of_arms (K0 Kc) HL (K0_secband Kc) A rho X HJI rest _ (HQIS rest) (HQIF rest)).
  - intros rest. exact (QC_step_of_full (K0 Kc) HL A rho X HJD HJI rest _ (HQCF rest)).
Qed.

Corollary drain_sum_of_arms3 : ltac2:(tb__ "0|0|
S20OF_;S19S1aR1A1S17SdR3S16R2A1A3S27SdR4S16R3A1A3S2eR5R4A2S37R6R5A2F_;F_;F_;F_;FKc;Fok;").
Proof. intros ok Kc HKc Hok Hokp HA. exact (drain_sum_of_arms2 ok Kc HKc Hok Hokp (q3_arms2_of_arms3 ok Kc HKc Hok Hokp HA)). Qed.
Corollary drain_sumE_of_arms3 : ltac2:(tb__ "0|0|
S19S1aR1A1S2fR2A1S38R3A1F_;F_;FKc;").
Proof. intros Kc HKc HA. exact (drain_sumE_of_arms2 Kc HKc (q3_arms2E_of_arms3 Kc HKc HA)). Qed.
End SegQ3M_sum.

(* [comment removed for export] *)
Module F0A_aLN1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "AE_A"; "J_free_preT"; "Pre_freeI"; "Wcan"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "true"; "pair"; "prod"; "bool"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "junkF"; "j_min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "aa_internal_inited"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "rigF"; "JF"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "le"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_cLN1"; "Erc_LN1"; "ED_LN1_1"; "ED_LN1_2"; "ED_LN1_3"; "TD_LN1_1"; "TD_LN1_2"; "TD_LN1_3"; "P0_LN1"; "PMID_LN1"; "exits1_LN1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMax"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "set_inited"; "IA_BEG"; "IA_END"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln"; "QFN"; "contN"; "econtN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skeln F0A_cLN1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.F0A_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_cLN1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lq.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ALN1.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).

Lemma spine_tail_LN1 : ltac2:(tb__ "0|2|
S0OF_;S1cOF_;S16S2S8S8SdScQ40M0A1A1S1dS3R5A1S22Vsegs;R8S20R6A1A3S25R6R5A2S27S36SbG0S9R6PdA2A2A2S23U1M1S1RcRbRaR9R7S2cS2fR5AaS23G1S1RdRcRbRaR8S2dS30R6AaS23G1S1ReRdRcRbR9S2eS31R7AaS41G1RfReRdRcRaS2bR8A8S44S8S3dS44R2S34A3S1fVsegs;R12S21Vsegs;S26G1S1SeR11R10ReA6R3R2RdA5RcA4F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HBIG E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 1) UStopLe) by apply stopJ_stable_le.
  unfold exits1_LN1 in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (f0_s2 1 UStopLe true S1c_LN1_1 C2_LN1_1 EfD_LN1_1 ED_LN1_1 run2_LN1_1 D2_LN1_1 W2_LN1_1 NX2_LN1_1 EQ2_LN1_1 RUN2_LN1_1 L2_LN1_1 AXD_LN1_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL.
    exact (f0_s3n 1 UStopLe TD_LN1_1 TDr_LN1_1 CD_LN1 Eps_LN1 Ebg_LN1 Erc_LN1 run3_LN1 AXDr_LN1_1 ENTD_LN1_1 RUN3_LN1 L3_LN1 NX3_LN1 SMF_LN1 CertR_LN1
             ok A' Kc rho rho1' tp' Q HUS HKc Hok (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
  - apply (f0_s2 1 UStopLe true S1c_LN1_2 C2_LN1_2 EfD_LN1_2 ED_LN1_2 run2_LN1_2 D2_LN1_2 W2_LN1_2 NX2_LN1_2 EQ2_LN1_2 RUN2_LN1_2 L2_LN1_2 AXD_LN1_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL.
    exact (f0_s3n 1 UStopLe TD_LN1_2 TDr_LN1_2 CD_LN1 Eps_LN1 Ebg_LN1 Erc_LN1 run3_LN1 AXDr_LN1_2 ENTD_LN1_2 RUN3_LN1 L3_LN1 NX3_LN1 SMF_LN1 CertR_LN1
             ok A' Kc rho rho1' tp' Q HUS HKc Hok (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
  - apply (f0_s2 1 UStopLe true S1c_LN1_3 C2_LN1_3 EfD_LN1_3 ED_LN1_3 run2_LN1_3 D2_LN1_3 W2_LN1_3 NX2_LN1_3 EQ2_LN1_3 RUN2_LN1_3 L2_LN1_3 AXD_LN1_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL.
    exact (f0_s3n 1 UStopLe TD_LN1_3 TDr_LN1_3 CD_LN1 Eps_LN1 Ebg_LN1 Erc_LN1 run3_LN1 AXDr_LN1_3 ENTD_LN1_3 RUN3_LN1 L3_LN1 NX3_LN1 SMF_LN1 CertR_LN1
             ok A' Kc rho rho1' tp' Q HUS HKc Hok (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
Qed.
Lemma espine_tail_LN1 : ltac2:(tb__ "0|2|
S0OF_;S16S2S8S8SdScQ40M0A1A1S1cOF_;S3R5A1S25R5R4A2S27S36SbG0S9R5PdA2A2A2S24U1M1S1RaR9R8R6S2cS2fR4A9S24G1S1RbRaR9R7S2dS30R5A9S24G1S1RcRbRaR8S2eS31R6A9S42G1RdRcRbR9S2bR7A7S44S8S3dS44R2S34A3S1eVsegs;S21Vsegs;S26G1S1SeR10RfRdA6R3R2RcA5RbA3F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HBIG E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 1) UStopLe) by apply stopJ_stable_le.
  unfold exits1_LN1 in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (ef0_s2 1 UStopLe true S1c_LN1_1 C2_LN1_1 EfD_LN1_1 ED_LN1_1 run2_LN1_1 D2_LN1_1 W2_LN1_1 NX2_LN1_1 EQ2_LN1_1 RUN2_LN1_1 L2_LN1_1 AXD_LN1_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL.
    exact (ef0_s3n 1 UStopLe TD_LN1_1 TDr_LN1_1 CD_LN1 Eps_LN1 Ebg_LN1 Erc_LN1 run3_LN1 AXDr_LN1_1 ENTD_LN1_1 RUN3_LN1 L3_LN1 NX3_LN1 SMF_LN1 NXB_LN1 ECertR_LN1
             A' Kc rho rho1' tp' Q HUS HKc (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
  - apply (ef0_s2 1 UStopLe true S1c_LN1_2 C2_LN1_2 EfD_LN1_2 ED_LN1_2 run2_LN1_2 D2_LN1_2 W2_LN1_2 NX2_LN1_2 EQ2_LN1_2 RUN2_LN1_2 L2_LN1_2 AXD_LN1_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL.
    exact (ef0_s3n 1 UStopLe TD_LN1_2 TDr_LN1_2 CD_LN1 Eps_LN1 Ebg_LN1 Erc_LN1 run3_LN1 AXDr_LN1_2 ENTD_LN1_2 RUN3_LN1 L3_LN1 NX3_LN1 SMF_LN1 NXB_LN1 ECertR_LN1
             A' Kc rho rho1' tp' Q HUS HKc (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
  - apply (ef0_s2 1 UStopLe true S1c_LN1_3 C2_LN1_3 EfD_LN1_3 ED_LN1_3 run2_LN1_3 D2_LN1_3 W2_LN1_3 NX2_LN1_3 EQ2_LN1_3 RUN2_LN1_3 L2_LN1_3 AXD_LN1_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL.
    exact (ef0_s3n 1 UStopLe TD_LN1_3 TDr_LN1_3 CD_LN1 Eps_LN1 Ebg_LN1 Erc_LN1 run3_LN1 AXDr_LN1_3 ENTD_LN1_3 RUN3_LN1 L3_LN1 NX3_LN1 SMF_LN1 NXB_LN1 ECertR_LN1
             A' Kc rho rho1' tp' Q HUS HKc (rigF_hd keep rho rho1 rho1' HR HL) ltac:(rewrite (proj1 HL 13%positive); exact Hn)
             (fun rhoE0 => HBIG A' rho1' rhoE0 tp' HDO HL) rhoX).
Qed.

Theorem free_spine_LN1 : ltac2:(tb__ "0|2|
S0OF_;S1cOF_;S16S2S8S8SdScQ40M0A1A1S1dS3R5A1S22Vsegs;R8S20R6A1A3S25R6R5A2S27S36SbG0S9R6PdA2A2A2S23U1M1S1RcRbRaR9R7S2cS2fR5AaS23G1S1RdRcRbRaR8S2dS30R6AaS23G1S1ReRdRcRbR9S2eS31R7AaS41G1RfReRdRcRaS2bR8A8S8S1fVsegs;R10S21Vsegs;S26G1S1SeRfReRcA6S32R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HBIG.
  apply (f0_s1c 1 UStopLe true P0_LN1 exits1_LN1 Cert1_LN1 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_LN1 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HBIG).
Qed.
Theorem efree_spine_LN1 : ltac2:(tb__ "0|2|
S0OF_;S16S2S8S8SdScQ40M0A1A1S1cOF_;S3R5A1S25R5R4A2S27S36SbG0S9R5PdA2A2A2S24U1M1S1RaR9R8R6S2cS2fR4A9S24G1S1RbRaR9R7S2dS30R5A9S24G1S1RcRbRaR8S2eS31R6A9S42G1RdRcRbR9S2bR7A7S8S1eVsegs;S21Vsegs;S26G1S1SeReRdRbA6S32R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HBIG.
  apply (ef0_s1c 1 UStopLe true P0_LN1 exits1_LN1 NX0_LN1 ECert1_LN1 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_LN1 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HBIG).
Qed.

Theorem free_spine_m_LN1 : ltac2:(tb__ "0|2|
S0OF_;S1cOF_;S16S2S8S8SdScQ40M0A1A1S1dS3R5A1S22Vsegs;R8S20R6A1A3S25R6R5A2S27S36SbG0S9R6PdA2A2A2S23U1M1S1RcRbRaR9R7S2cS2fR5AaS23G1S1RdRcRbRaR8S2dS30R6AaS23G1S1ReRdRcRbR9S2eS31R7AaS41G1RfReRdRcRaS2bR8A8S8S1fVsegs;R10S21Vsegs;S26G1S1SeRfReRcA6S33R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HBIG.
  apply (f0_s1c 1 UStopLe true PMID_LN1 exits1_LN1 Cert1m_LN1 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_LN1 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HBIG).
Qed.
Theorem efree_spine_m_LN1 : ltac2:(tb__ "0|2|
S0OF_;S16S2S8S8SdScQ40M0A1A1S1cOF_;S3R5A1S25R5R4A2S27S36SbG0S9R5PdA2A2A2S24U1M1S1RaR9R8R6S2cS2fR4A9S24G1S1RbRaR9R7S2dS30R5A9S24G1S1RcRbRaR8S2eS31R6A9S42G1RdRcRbR9S2bR7A7S8S1eVsegs;S21Vsegs;S26G1S1SeReRdRbA6S33R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HBIG.
  apply (ef0_s1c 1 UStopLe true PMID_LN1 exits1_LN1 NX0m_LN1 ECert1m_LN1 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_LN1 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HBIG).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S0S46VCST;R1A2S1bS47R2A1A1F_;Fa;").

Theorem hdf_LN1_1 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S3eS0S0S0S14S3R8A1S39SaRaR8R7R6A5S3dS10S0S0A2SfS0S0R6R5A4S17RbA1A3S3fR7R6A2S19S0SbG0S9RbPcA2A2R8A3S35ReRcR9R8R7R6A6S1cOF_;S1dS22SaR2S20R10A1A3S43SaR3S20R11A1A3S23U1S1S2aVCST;VXGL;R13A3R4R13R12S13R13R11ReRdRcRbA6S2cS2fR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] ok Q Hok Hokp.
  exact (depot_call_HDFG 1 (rd_okG NVN 1) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LN1_1 TD_LN1_1 (sD_of ED_LN1_1 1) RD_LN1_1 HeD_LN1_1 HchkD_LN1_1 HTD_LN1_1 DCHK_LN1_1
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 1) ok Q Hok Hokp).
Qed.
Theorem hdfe_LN1_1 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S3eS0S0S0S14S3R8A1S39SaRaR8R7R6A5S3dS10S0S0A2SfS0S0R6R5A4S17RbA1A3S3fR7R6A2S19S0SbG0S9RbPcA2A2R8A3S35ReRcR9R8R7R6A6S1cOF_;S24U1S1S2aVCST;VXGL;R10A3R10RfS13R10ReRbRaR9R8A6S2cS2fR1A9FQ;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] Q.
  exact (depot_call_HDFEG 1 (rd_okG NVN 1) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LN1_1 TD_LN1_1 (sD_of ED_LN1_1 1) RD_LN1_1 HeD_LN1_1 HchkD_LN1_1 HTD_LN1_1 DCHK_LN1_1
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 1) Q).
Qed.
Theorem hdf_LN1_2 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S3eS0S0S0S14S3R8A1S39SaRaR8R7R6A5S3dS10S0S0A2SfS0S0R6R5A4S17RbA1A3S3fR7R6A2S19S0SbG0S9RbPcA2A2R8A3S35ReRcR9R8R7R6A6S1cOF_;S1dS22SaR2S20R10A1A3S43SaR3S20R11A1A3S23U1S1S2aVCST;VXGL;R13A3R4R13R12S13R13R11ReRdRcRbA6S2dS30R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] ok Q Hok Hokp.
  exact (depot_call_HDFG 1 (rd_okG NVN 1) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LN1_2 TD_LN1_2 (sD_of ED_LN1_2 2) RD_LN1_2 HeD_LN1_2 HchkD_LN1_2 HTD_LN1_2 DCHK_LN1_2
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 1) ok Q Hok Hokp).
Qed.
Theorem hdfe_LN1_2 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S3eS0S0S0S14S3R8A1S39SaRaR8R7R6A5S3dS10S0S0A2SfS0S0R6R5A4S17RbA1A3S3fR7R6A2S19S0SbG0S9RbPcA2A2R8A3S35ReRcR9R8R7R6A6S1cOF_;S24U1S1S2aVCST;VXGL;R10A3R10RfS13R10ReRbRaR9R8A6S2dS30R1A9FQ;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] Q.
  exact (depot_call_HDFEG 1 (rd_okG NVN 1) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LN1_2 TD_LN1_2 (sD_of ED_LN1_2 2) RD_LN1_2 HeD_LN1_2 HchkD_LN1_2 HTD_LN1_2 DCHK_LN1_2
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 1) Q).
Qed.
Theorem hdf_LN1_3 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S3eS0S0S0S14S3R8A1S39SaRaR8R7R6A5S3dS10S0S0A2SfS0S0R6R5A4S17RbA1A3S3fR7R6A2S19S0SbG0S9RbPcA2A2R8A3S35ReRcR9R8R7R6A6S1cOF_;S1dS22SaR2S20R10A1A3S43SaR3S20R11A1A3S23U1S1S2aVCST;VXGL;R13A3R4R13R12S13R13R11ReRdRcRbA6S2eS31R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] ok Q Hok Hokp.
  exact (depot_call_HDFG 1 (rd_okG NVN 1) 3 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LN1_3 TD_LN1_3 (sD_of ED_LN1_3 3) RD_LN1_3 HeD_LN1_3 HchkD_LN1_3 HTD_LN1_3 DCHK_LN1_3
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 1) ok Q Hok Hokp).
Qed.
Theorem hdfe_LN1_3 : ltac2:(tb__ "0|1|
S16S2S8SdScQ40M0A1A1S3eS0S0S0S14S3R8A1S39SaRaR8R7R6A5S3dS10S0S0A2SfS0S0R6R5A4S17RbA1A3S3fR7R6A2S19S0SbG0S9RbPcA2A2R8A3S35ReRcR9R8R7R6A6S1cOF_;S24U1S1S2aVCST;VXGL;R10A3R10RfS13R10ReRbRaR9R8A6S2eS31R1A9FQ;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] Q.
  exact (depot_call_HDFEG 1 (rd_okG NVN 1) 3 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LN1_3 TD_LN1_3 (sD_of ED_LN1_3 3) RD_LN1_3 HeD_LN1_3 HchkD_LN1_3 HTD_LN1_3 DCHK_LN1_3
           A Kc (rhoF_of A rho p n t jv) HKc (rd_zone_N A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV 1) Q).
Qed.

Theorem free_lo_N_1 : ltac2:(tb__ "0|3|
S1cOF_;S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S40VCST;VXGL;U1M1R6R5R4R3A7S1dS3R6A1S22SaR9S20R7A1A3S43SaRaS20R8A1A3S28S29R6R5A2S37A2S19S11S18RbA1SeA3S27S36R7A2S0S14S35RfRdRbRaR2R1A6S19S0S15R2A1S38A3S25RfS13R11RfRdRcR4R3A6A2S41G1S2aVCST;VXGL;R12A3R13R12R11S13R12R10ReRdR5R4A6S2bRcA8F_;F_;F_;Fjv;Ft;S1fSaRfS21SaS5S39SaA1S7G1A1M2S1ReRdA5S6S4G2S1A3RcRbA5R8A4F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii HBG HBIG. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (entry_pureN false (Wcan 1) UStopLe A rho)); [intros w Hw; exact (entry_pure_N false _ _ A Kc rho tp w HHI Hii HBG Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros k Hg w Hw.
  destruct (g_instantiate false 1 UStopLe NVN VFN Wa_LN1 Da_LN1 Wb_LN1 Wc_LN1 Wd_LN1 Fb_LN1 XI_LN1 A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree A rho p n t jv) IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A rho p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl); exact HBG).
  exact (free_spine_LN1 (KEEPD CST XGL A) ok A Kc rho (rhoF_of A rho p n t jv) tp Q HKc Hok HR Hn1
           (hdf_LN1_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ ok _ Hok Hokp) (hdf_LN1_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ ok _ Hok Hokp) (hdf_LN1_3 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ ok _ Hok Hokp)
           (HBIG t jv HTJ HJM HR) (rhoF_of A rho p n t jv) k Hg w Hw1).
Qed.
Theorem efree_lo_N_1 : ltac2:(tb__ "0|3|
S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S40VCST;VXGL;U1M1R6R5R4R3A7S1dS3R6A1S28S29R4R3A2S37A2S19S11S18R9A1SeA3S27S36R5A2S0S14S35RdRbR9R8R2R1A6S19S0S15R2A1S38A3S25RdS13RfRdRbRaR4R3A6A2S42G1S2aVCST;VXGL;R10A3R10RfS13R10ReRcRbR5R4A6S2bRaA7F_;F_;F_;Fjv;Ft;S1eSaS21SaS5S39SaA1S7G1A1M2S1RcRbA5S6S4G2S1A3RaR9A5R6A3F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii HBG HBIG. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (entry_pureN false (Wcan 1) UStopLe A rho)); [intros w Hw; exact (entry_pure_N false _ _ A Kc rho tp w HHI Hii HBG Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros w Hw.
  destruct (g_instantiate false 1 UStopLe NVN VFN Wa_LN1 Da_LN1 Wb_LN1 Wc_LN1 Wd_LN1 Fb_LN1 XI_LN1 A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree A rho p n t jv) IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A rho p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl); exact HBG).
  exact (efree_spine_LN1 (KEEPD CST XGL A) A Kc rho (rhoF_of A rho p n t jv) tp Q HKc HR Hn1
           (hdfe_LN1_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ _) (hdfe_LN1_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ _) (hdfe_LN1_3 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ _)
           (HBIG t jv HTJ HJM HR) (rhoF_of A rho p n t jv) w Hw1).
Qed.

Hypothesis HCST2 : ltac2:(tb__ "0|0|
S0S46VCST;R1A2S1aS1bS1aS28S3bR2A2S27R2S3cA2A2A1S1bS1aS28Z17db48R2A2S27R2Z17db4cA2A2A1A2F_;Fa;").
Theorem free_lo_ia0_N_1 : ltac2:(tb__ "0|4|
S1cOF_;S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S40VCST;VXGL;U1M1R6R5R4R3A7S1dS3R6A1S22SaR9S20R7A1A3S43SaRaS20R8A1A3S28S29R6R5A2S37A2S19S11S18RbA1S12A3S27S36R7A2S8S0S14S45R10S13R10ReRcRbR2R1A6R3A3S35S3aR11A1R4RdRcR3R2A6S19S0S15R3A1S38A3S25R6S13S3aR13A1R6RfReR5R4A6A2S41G1S2aVCST;VXGL;S3aR14A1M2A3R15G2R13S13G2R7R10RfR6R5A6S2bS40VCST;VXGL;G1G2R13R7R11A7A8F_;F_;F_;F_;Fjv;Ft;Frho2;S1fSaRfS21SaS5S39SaA1S7G1A1M3S1ReRdA5S6S4G3S1A3RcRbA5R8A4F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii HBG HBIG. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix 1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lq.F0A_m1A.Wai_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lq.F0A_m1A.Dai_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lq.F0A_m1A.Wbi_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lq.F0A_m1A.Wci_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lq.F0A_m1A.Certi_1A ok A Kc rho tp Q p n t jv Hii HKc Hok).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 1 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (triple_pre_pure segsA ok _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instG_facts false (Wcan 1) UStopLe NVN VFN (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_N A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 1) UStopLe HHI HBG). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (g_instantiate_mid false 1 UStopLe NVN VFN Wbm_LN1 Wcm_LN1 Wdm_LN1 Fb_LN1 XIm_LN1 A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A1 rho2 p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl), E13; exact HBG).
  exact (free_spine_m_LN1 (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR Hn1
           (hdf_LN1_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ ok _ Hok Hokp) (hdf_LN1_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ ok _ Hok Hokp) (hdf_LN1_3 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR) (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.
Theorem efree_lo_ia0_N_1 : ltac2:(tb__ "0|4|
S16S2S8SdScQ40M0A1A1SbG0S9R2PcA2A2S0SbG0S9R3PdA2A2S0S40VCST;VXGL;U1M1R6R5R4R3A7S1dS3R6A1S28S29R4R3A2S37A2S19S11S18R9A1S12A3S27S36R5A2S8S0S14S45ReS13ReRcRaR9R2R1A6R3A3S35S3aRfA1R4RbRaR3R2A6S19S0S15R3A1S38A3S25R6S13S3aR11A1R6RdRcR5R4A6A2S42G1S2aVCST;VXGL;S3aR12A1M2A3G2R11S13G2R7ReRdR6R5A6S2bS40VCST;VXGL;G1G2R11R7RfA7A7F_;F_;F_;F_;Fjv;Ft;Frho2;S1eSaS21SaS5S39SaA1S7G1A1M3S1RcRbA5S6S4G3S1A3RaR9A5R6A3F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii HBG HBIG. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix 1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lq.F0A_m1A.Wai_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lq.F0A_m1A.Dai_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lq.F0A_m1A.Wbi_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lq.F0A_m1A.Wci_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lq.F0A_m1A.ECerti_1A A Kc rho tp Q p n t jv Hii HKc).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 1 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (etriple_pre_pure segsA _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instG_facts false (Wcan 1) UStopLe NVN VFN (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_N A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 1) UStopLe HHI HBG). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (g_instantiate_mid false 1 UStopLe NVN VFN Wbm_LN1 Wcm_LN1 Wdm_LN1 Fb_LN1 XIm_LN1 A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  assert (Hn1 : kQuarantineMax < bv_unsigned (rw (rhoF_of A1 rho2 p n t jv) 13%positive)) by (rewrite <- (proj1 (rg_agree _ _ HR) 13%positive eq_refl), E13; exact HBG).
  exact (efree_spine_m_LN1 (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR Hn1
           (hdfe_LN1_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ _) (hdfe_LN1_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ _) (hdfe_LN1_3 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ _)
           (HBIG rho2 t jv ML HTJ JM HR) (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End ALN1.
End F0A_aLN1.

