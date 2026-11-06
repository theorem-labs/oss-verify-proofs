(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cu cv.
From Stdlib Require Permutation FunctionalExtensionality.

(* [comment removed for export] *)
Module SpineCallocSec6J.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "list"; "prod"; "length"; "pair"; "None"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "sobj"; "rl"; "sv"; "holds"; "sprop"; "SVar"; "eval"; "obj_range"; "SAlu"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "DG"; "aa_sec"; "sec_chunk"; "aa_Km"; "aa_ptr_committed"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "div"; "of_nat"; "lt"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS"; "AXK"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "JGs"; "range_noband"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3I"; "nx0"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump"; "bumpP"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv"; "bumpV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "JLc_ok"; "Lc_ok"; "PFc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "V_NRES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineCallocSec5I"; "C5ac"; "C5bc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cu.SpineCallocSec6I"; "FXPa"; "FXPb"; "PXa"; "PXb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec7"; "bx_ok"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2"; "IMG_S"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec4I.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ch.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec4I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CertCallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cc.SpineCallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineCallocSec5I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cu.SpineCallocSec6I.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.GS nx0.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S6S41VCST;R1A2S41S53R2A2S1eF_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S6S41VCST;R1A2S41S54R2A2S1eF_;F_;Fa;").

Lemma PXnba_0 : ltac2:(tb__ "0|2|
S16S15S2aS8S27Q40A1M0S8S0G0A1S0S35A1S34S2dU0Vst;S2fS26S15S33R1A1LX;R9A2R8R7R6R5R4R3R2R1AcS30SfSeR5A1S4dA3S0SbA1S1bS0S1S1SdSdA2SdA2M1A1S31SbG1S43R1A4S31SbG1S43S4fA4A3S30SbSbS2eS12R9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FG2;").
Proof.
  intros G2 A Kc rho a r tp tr md HJ HF.
  exact (pxa_noband 0%nat st tmax nx0 Hnx_0 (AXK (fun X : AA => bumpP X) G2) A Kc rho a r tp tr md (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HF).
Qed.
Lemma BXoka_0 : ltac2:(tb__ "0|0|
S16S51S26S15S33R1A1LX;R1A2A1FG2;").
Proof. intros G2 X. repeat split; reflexivity. Qed.
Lemma HPATHa_0 : ltac2:(tb__ "0|6|
S16S15S2aS8S27Q40M0A1M1S8S0G1A1S0S35A1S34S2dU0Vst;S2fS26S15S33R1A1LX;M2R9A2R8R7R6R5R4R3R2R1AcS30SfSeR5A1S4dA3S26G2RbS46RaS28G0S9R8PcA2A2A2A3S15S1cS1cS20Z8M3Z20000M4A2S20G4G4A2A2S1cS20S21S25G3S23S2S18S17RbA1A2A1A2G4A2S1aR1A1M5A2S1bG1S11R7S13S52S10S4aA1S14Z4000A1A3A2S29G0S22G5G3A2A2A3A2A2TAs;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FG2;").
Proof.
  intros G2 A Kc rho a r tp tr md HJ HF.
  exact (hpath_a 0%nat st tmax nx0 Hnx_0 (AXK (fun X : AA => bumpP X) G2) A Kc rho a r tp tr md (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HF).
Qed.

Theorem sec_tail_0ha_P : ltac2:(tb__ "0|9|
S37OF_;S15S2aS8S8S27Q40M0A1M1S0G1A1M2S16S0S1S3cS3eA2M3A1S32G3S3S3cS3eS48VW;Vst;A2S47VCST;VXGL;R8R7A4A4R1A3S45VW;Vst;A2S2bR9A1S3bS1fRcS3aRaA1A3S7S1bG1S9RaR1A2S9RbR1A2A3Fi;S7S1bS0S27Q8A1M4A1ScRbR1A2ScRcR1A2A3Fl;S2cVCST;VXGL;ReReSaRcA1SaRbA1A6S20S23S2S18S17RfA1A2A1S19RfA1A2S1S6S6A2M5S32G5R1S42RbA1A3S40R2S3S6S6S28G0ReA2M6S44S28G0S9RfPcA2A2A1M7A4A2F_;Fbn;S6S1cS20S3fG6A1M8R1A2S24R1S21G8S22G7Z8A2A2A2A2S1dS1bS5G4A1SaR10S29G0R2A2A2S4G4A1A3A1F_;Fz;S8G2S36S1fR15S39S1fS2dU0Vst;S2fS26S15S33R1A1LX;ReA2R14R13R11R10A8S4bR2R1A5S3dS1fS38R12RfRdA5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 G2 Posts HPin HUS HKc Hokl HLw HLl HKEPT HL9 HDB RUNDEF.
  set (BX := AXK (fun X : AA => bumpP X) G2). set (Q := LQPA segsA NF rho0 tp0 Posts).
  assert (HW : stopJ_w W st) by (hw_discharge).
  assert (BXg : forall X, aa_geom (BX X) = aa_geom X) by (intros X; reflexivity).
  apply (sec_g43 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXa FXPa (PXnba_0 G2) C5ac C5Aa C5Ba Y6Aa Y6Ba E6a CT6a CO6a T6a s6Aa s6Ba s6a R6a
           HC5Aa_0 HC5Ba_0 FBAa_0 FBBa_0 Cert6Aa_0 Cert6Ba_0 E6Aa_0 I6Aa_0 E6Ba_0 I6Ba_0
           WC6a_0 DF6a_0 NX6a_0 HC6a_0 SK6a_0 FC6a_0 FX6a_0 XC6a_0 HCO6a_0 WCO6a_0 He6a_0 Hchk6a_0 HT6a_0 FBC6a_0 FBT6a_0 NXC6a_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY6 tY6. rewrite HD6a_0.
  apply (sec_g44 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXa FXPa (PXnba_0 G2) D6a U7a ET7a CT7a CO7a CR7a CS7a CM7a T7a s7a R7a n7a
           WU7a_0 DU7a_0 NXU7a_0 HU7a_0 Cert7a_0 WC7a_0 DF7a_0 NX7a_0 HC7a_0 SK7a_0 FC7a_0 FX7a_0 XC7a_0 HCO7a_0 WCO7a_0
           RB7a_0 HCR7a_0 LEN7a_0 PERM_nd7a_0 PERM_lt7a_0 PERM_cov7a_0 HCS7a_0 MRG7a_0 HCM7a_0 He7a_0 Hchk7a_0 HT7a_0 FBC7a_0 FBT7a_0 NXC7a_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY7 tY7. rewrite HD7a_0.
  apply (sec_g45 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXa FXPa (PXnba_0 G2) D7a U8a ET8a CT8a CO8a T8a s8a R8a
           WU8a_0 DU8a_0 NXU8a_0 HU8a_0 Cert8a_0 WC8a_0 DF8a_0 NX8a_0 HC8a_0 SK8a_0 FC8a_0 FX8a_0 XC8a_0 HCO8a_0 WCO8a_0
           He8a_0 Hchk8a_0 HT8a_0 FBC8a_0 FBT8a_0 NXC8a_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY8 tY8. rewrite HD8a_0.
  apply (sec_g46 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXa FXPa (PXnba_0 G2) D8a U9a E9fa E9pa CO9pa E9qa
           WU9a_0 DU9a_0 NXU9a_0 HU9a_0 Cert9a_0 SK9a_0 FC9a_0 FX9a_0 FP9a_0 XC9a_0 HCO9a_0 WCO9a_0 Cert9qa_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  - intros rY9 tY9.
    apply (sec_g47d 0%nat st tmax nx0 Hnx_0 BX E9fa S9afa S9bfa D9fa iMfa perm9fa HS9afa_0 HS9bfa_0 HD9fa_0 NDpfa_0 BNDpfa_0 COVpfa_0 BXg D9faA D9faB HD9Afa_0 HD9Bfa_0 FBA9fa_0 FBB9fa_0 ok A Kc rho a Q).
    + intros rZ tZ.
      exact (sec_g48_P 0%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXoka_0 G2) 131072 DZero (SAlu ALU_ADD (SVar V_NRES) (SLit 16384)) FXPa ltac:(first [left; reflexivity | right; reflexivity]) (HPATHa_0 G2)
             false FFfaA swcfaA c1faA c2faA c4faA c5faA mcfaA xcfaA tybfaA SELFfaA_0 NDFfaA_0 BNDFfaA_0 COVFfaA_0 XFnfaA_0 BFbfaA_0 FPFfaA_0 FXFfaA_0 FPARfaA_0
             Hc1faA_0 HmcfaA_0 HtybfaA_0 HxcfaA_0 WCUfaA_0 SELUfaA_0 NDUfaA_0 BNDUfaA_0 COVUfaA_0 W9faA_0 D9faA_0 XB9faA_0 sFfaA ENT9faA_0 SID9faA_0 G110faA_0 D9faA CertFfaA_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
    + intros rZ tZ.
      exact (sec_g48_P 0%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXoka_0 G2) 131072 DZero (SAlu ALU_ADD (SVar V_NRES) (SLit 16384)) FXPa ltac:(first [left; reflexivity | right; reflexivity]) (HPATHa_0 G2)
             false FFfaB swcfaB c1faB c2faB c4faB c5faB mcfaB xcfaB tybfaB SELFfaB_0 NDFfaB_0 BNDFfaB_0 COVFfaB_0 XFnfaB_0 BFbfaB_0 FPFfaB_0 FXFfaB_0 FPARfaB_0
             Hc1faB_0 HmcfaB_0 HtybfaB_0 HxcfaB_0 WCUfaB_0 SELUfaB_0 NDUfaB_0 BNDUfaB_0 COVUfaB_0 W9faB_0 D9faB_0 XB9faB_0 sFfaB ENT9faB_0 SID9faB_0 G110faB_0 D9faB CertFfaB_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
  - intros rY9 tY9.
    apply (sec_g47d 0%nat st tmax nx0 Hnx_0 BX E9qa S9aqa S9bqa D9qa iMqa perm9qa HS9aqa_0 HS9bqa_0 HD9qa_0 NDpqa_0 BNDpqa_0 COVpqa_0 BXg D9qaA D9qaB HD9Aqa_0 HD9Bqa_0 FBA9qa_0 FBB9qa_0 ok A Kc rho a Q).
    + intros rZ tZ.
      exact (sec_g48_P 0%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXoka_0 G2) 131072 DZero (SAlu ALU_ADD (SVar V_NRES) (SLit 16384)) FXPa ltac:(first [left; reflexivity | right; reflexivity]) (HPATHa_0 G2)
             true FFqaA swcqaA c1qaA c2qaA c4qaA c5qaA mcqaA xcqaA tybqaA SELFqaA_0 NDFqaA_0 BNDFqaA_0 COVFqaA_0 XFnqaA_0 BFbqaA_0 FPFqaA_0 FXFqaA_0 FPARqaA_0
             Hc1qaA_0 HmcqaA_0 HtybqaA_0 HxcqaA_0 WCUqaA_0 SELUqaA_0 NDUqaA_0 BNDUqaA_0 COVUqaA_0 W9qaA_0 D9qaA_0 XB9qaA_0 sFqaA ENT9qaA_0 SID9qaA_0 G110qaA_0 D9qaA CertFqaA_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
    + intros rZ tZ.
      exact (sec_g48_P 0%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXoka_0 G2) 131072 DZero (SAlu ALU_ADD (SVar V_NRES) (SLit 16384)) FXPa ltac:(first [left; reflexivity | right; reflexivity]) (HPATHa_0 G2)
             true FFqaB swcqaB c1qaB c2qaB c4qaB c5qaB mcqaB xcqaB tybqaB SELFqaB_0 NDFqaB_0 BNDFqaB_0 COVFqaB_0 XFnqaB_0 BFbqaB_0 FPFqaB_0 FXFqaB_0 FPARqaB_0
             Hc1qaB_0 HmcqaB_0 HtybqaB_0 HxcqaB_0 WCUqaB_0 SELUqaB_0 NDUqaB_0 BNDUqaB_0 COVUqaB_0 W9qaB_0 D9qaB_0 XB9qaB_0 sFqaB ENT9qaB_0 SID9qaB_0 G110qaB_0 D9qaB CertFqaB_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
Qed.

Theorem sec_tail_0ha : ltac2:(tb__ "0|8|
S37OF_;S15S2aS8S8S27Q40M0A1M1S0G1A1M2S16S45VW;Vst;A2S2bR7A1S3bS1fRaS3aR8A1A3S7S1bG1S9R8R1A2S9R9R1A2A3Fi;S7S1bS0S27Q8A1M3A1ScR9R1A2ScRaR1A2A3Fl;S2cVCST;VXGL;RcRcSaRaA1SaR9A1A6S20S23S2S18S17RdA1A2A1S19RdA1A2S1S6S6A2M4S32G4R1S42R9A1A3S40R2S3S6S6S28G0RcA2M5S44S28G0S9RdPcA2A2A1M6A4A2F_;Fbn;S6S1cS20S3fG5A1M7R1A2S24R1S21G7S22G6Z8A2A2A2A2S1dS1bS5G3A1SaReS29G0R2A2A2S4G3A1A3A1F_;Fz;S8G2S36S1fR13S39S1fS2dU0Vst;S2fS26S15S33R1A1LX;RcA2R12R11RfReA8S4bR2R1A5S3dS1fS38R10RdS49VCST;VXGL;VW;Vst;R12R11A6A5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 G2. exact (sec_tail_0ha_P ok A Kc rho0 rho a tp0 G2 (PFc CST XGL W st A Kc) (or_intror (or_introl eq_refl))).
Qed.

Lemma PXnbb_0 : ltac2:(tb__ "0|2|
S16S15S2aS8S27Q40A1M0S8S0G0A1S0S35A1S34S2dU0Vst;S2fS26S15R1LX;R9A2R8R7R6R5R4R3R2R1AcS30SfSeR5A1S4eA3S0SbA1S1bS0S1S1SdSdA2SdA2M1A1S31SbG1S43R1A4S31SbG1S43S50A4A3S30SbSbS2eS12R9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FG2;").
Proof.
  intros G2 A Kc rho a r tp tr md HJ HF.
  exact (pxb_noband 0%nat st tmax nx0 Hnx_0 (AXK (fun X : AA => X) G2) A Kc rho a r tp tr md (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HF).
Qed.
Lemma BXokb_0 : ltac2:(tb__ "0|0|
S16S51S26S15R1LX;R1A2A1FG2;").
Proof. intros G2 X. repeat split; reflexivity. Qed.
Lemma HPATHb_0 : ltac2:(tb__ "0|5|
S16S15S2aS8S27Q40M0A1M1S8S0G1A1S0S35A1S34S2dU0Vst;S2fS26S15R1LX;M2R9A2R8R7R6R5R4R3R2R1AcS30SfSeR5A1S4eA3S26G2RbS46RaS28G0S9R8PcA2A2A2A3S15S1cS1cS20Z8M3G3A2S20G3Z20000A2A2S1cS20S21S25G3S23S2S18S17RbA1A2A1A2G3A2S1aR1A1M4A2S1bG1S11R7S10S4aA1A2S29G0S22G4G3A2A2A3A2A2TAs;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FG2;").
Proof.
  intros G2 A Kc rho a r tp tr md HJ HF.
  exact (hpath_b 0%nat st tmax nx0 Hnx_0 (AXK (fun X : AA => X) G2) A Kc rho a r tp tr md (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HF).
Qed.

Theorem sec_tail_0hb_P : ltac2:(tb__ "0|9|
S37OF_;S15S2aS8S8S27Q40M0A1M1S0G1A1M2S16S0S1S3cS3eA2M3A1S32G3S3S3cS3eS48VW;Vst;A2S47VCST;VXGL;R8R7A4A4R1A3S45VW;Vst;A2S2bR9A1S3bS1fRcS3aRaA1A3S7S1bG1S9RaR1A2S9RbR1A2A3Fi;S7S1bS0S27Q8A1M4A1ScRbR1A2ScRcR1A2A3Fl;S2cVCST;VXGL;ReReSaRcA1SaRbA1A6S20S23S2S18S17RfA1A2A1S19RfA1A2S1S6S6A2M5S32G5R1S42RbA1A3S40R2S3S6S6S28G0ReA2M6S44S28G0S9RfPcA2A2A1M7A4A2F_;Fbn;S6S1cS20S3fG6A1M8R1A2S24R1S21G8S22G7Z8A2A2A2A2S1dS1bS5G4A1SaR10S29G0R2A2A2S4G4A1A3A1F_;Fz;S8G2S36S1fR15S39S1fS2dU0Vst;S2fS26S15R1LX;ReA2R14R13R11R10A8S4cR2R1A5S3dS1fS38R12RfRdA5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 G2 Posts HPin HUS HKc Hokl HLw HLl HKEPT HL9 HDB RUNDEF.
  set (BX := AXK (fun X : AA => X) G2). set (Q := LQPA segsA NF rho0 tp0 Posts).
  assert (HW : stopJ_w W st) by (hw_discharge).
  assert (BXg : forall X, aa_geom (BX X) = aa_geom X) by (intros X; reflexivity).
  apply (sec_g43 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXb FXPb (PXnbb_0 G2) C5bc C5Ab C5Bb Y6Ab Y6Bb E6b CT6b CO6b T6b s6Ab s6Bb s6b R6b
           HC5Ab_0 HC5Bb_0 FBAb_0 FBBb_0 Cert6Ab_0 Cert6Bb_0 E6Ab_0 I6Ab_0 E6Bb_0 I6Bb_0
           WC6b_0 DF6b_0 NX6b_0 HC6b_0 SK6b_0 FC6b_0 FX6b_0 XC6b_0 HCO6b_0 WCO6b_0 He6b_0 Hchk6b_0 HT6b_0 FBC6b_0 FBT6b_0 NXC6b_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY6 tY6. rewrite HD6b_0.
  apply (sec_g44 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXb FXPb (PXnbb_0 G2) D6b U7b ET7b CT7b CO7b CR7b CS7b CM7b T7b s7b R7b n7b
           WU7b_0 DU7b_0 NXU7b_0 HU7b_0 Cert7b_0 WC7b_0 DF7b_0 NX7b_0 HC7b_0 SK7b_0 FC7b_0 FX7b_0 XC7b_0 HCO7b_0 WCO7b_0
           RB7b_0 HCR7b_0 LEN7b_0 PERM_nd7b_0 PERM_lt7b_0 PERM_cov7b_0 HCS7b_0 MRG7b_0 HCM7b_0 He7b_0 Hchk7b_0 HT7b_0 FBC7b_0 FBT7b_0 NXC7b_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY7 tY7. rewrite HD7b_0.
  apply (sec_g45 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXb FXPb (PXnbb_0 G2) D7b U8b ET8b CT8b CO8b T8b s8b R8b
           WU8b_0 DU8b_0 NXU8b_0 HU8b_0 Cert8b_0 WC8b_0 DF8b_0 NX8b_0 HC8b_0 SK8b_0 FC8b_0 FX8b_0 XC8b_0 HCO8b_0 WCO8b_0
           He8b_0 Hchk8b_0 HT8b_0 FBC8b_0 FBT8b_0 NXC8b_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY8 tY8. rewrite HD8b_0.
  apply (sec_g46 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXb FXPb (PXnbb_0 G2) D8b U9b E9fb E9pb CO9pb E9qb
           WU9b_0 DU9b_0 NXU9b_0 HU9b_0 Cert9b_0 SK9b_0 FC9b_0 FX9b_0 FP9b_0 XC9b_0 HCO9b_0 WCO9b_0 Cert9qb_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  - intros rY9 tY9.
    apply (sec_g47d 0%nat st tmax nx0 Hnx_0 BX E9fb S9afb S9bfb D9fb iMfb perm9fb HS9afb_0 HS9bfb_0 HD9fb_0 NDpfb_0 BNDpfb_0 COVpfb_0 BXg D9fbA D9fbB HD9Afb_0 HD9Bfb_0 FBA9fb_0 FBB9fb_0 ok A Kc rho a Q).
    + intros rZ tZ.
      exact (sec_g48_P 0%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXokb_0 G2) 8 DUnknown (SVar V_NRES) FXPb ltac:(first [left; reflexivity | right; reflexivity]) (HPATHb_0 G2)
             false FFfbA swcfbA c1fbA c2fbA c4fbA c5fbA mcfbA xcfbA tybfbA SELFfbA_0 NDFfbA_0 BNDFfbA_0 COVFfbA_0 XFnfbA_0 BFbfbA_0 FPFfbA_0 FXFfbA_0 FPARfbA_0
             Hc1fbA_0 HmcfbA_0 HtybfbA_0 HxcfbA_0 WCUfbA_0 SELUfbA_0 NDUfbA_0 BNDUfbA_0 COVUfbA_0 W9fbA_0 D9fbA_0 XB9fbA_0 sFfbA ENT9fbA_0 SID9fbA_0 G110fbA_0 D9fbA CertFfbA_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
    + intros rZ tZ.
      exact (sec_g48_P 0%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXokb_0 G2) 8 DUnknown (SVar V_NRES) FXPb ltac:(first [left; reflexivity | right; reflexivity]) (HPATHb_0 G2)
             false FFfbB swcfbB c1fbB c2fbB c4fbB c5fbB mcfbB xcfbB tybfbB SELFfbB_0 NDFfbB_0 BNDFfbB_0 COVFfbB_0 XFnfbB_0 BFbfbB_0 FPFfbB_0 FXFfbB_0 FPARfbB_0
             Hc1fbB_0 HmcfbB_0 HtybfbB_0 HxcfbB_0 WCUfbB_0 SELUfbB_0 NDUfbB_0 BNDUfbB_0 COVUfbB_0 W9fbB_0 D9fbB_0 XB9fbB_0 sFfbB ENT9fbB_0 SID9fbB_0 G110fbB_0 D9fbB CertFfbB_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
  - intros rY9 tY9.
    apply (sec_g47d 0%nat st tmax nx0 Hnx_0 BX E9qb S9aqb S9bqb D9qb iMqb perm9qb HS9aqb_0 HS9bqb_0 HD9qb_0 NDpqb_0 BNDpqb_0 COVpqb_0 BXg D9qbA D9qbB HD9Aqb_0 HD9Bqb_0 FBA9qb_0 FBB9qb_0 ok A Kc rho a Q).
    + intros rZ tZ.
      exact (sec_g48_P 0%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXokb_0 G2) 8 DUnknown (SVar V_NRES) FXPb ltac:(first [left; reflexivity | right; reflexivity]) (HPATHb_0 G2)
             true FFqbA swcqbA c1qbA c2qbA c4qbA c5qbA mcqbA xcqbA tybqbA SELFqbA_0 NDFqbA_0 BNDFqbA_0 COVFqbA_0 XFnqbA_0 BFbqbA_0 FPFqbA_0 FXFqbA_0 FPARqbA_0
             Hc1qbA_0 HmcqbA_0 HtybqbA_0 HxcqbA_0 WCUqbA_0 SELUqbA_0 NDUqbA_0 BNDUqbA_0 COVUqbA_0 W9qbA_0 D9qbA_0 XB9qbA_0 sFqbA ENT9qbA_0 SID9qbA_0 G110qbA_0 D9qbA CertFqbA_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
    + intros rZ tZ.
      exact (sec_g48_P 0%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXokb_0 G2) 8 DUnknown (SVar V_NRES) FXPb ltac:(first [left; reflexivity | right; reflexivity]) (HPATHb_0 G2)
             true FFqbB swcqbB c1qbB c2qbB c4qbB c5qbB mcqbB xcqbB tybqbB SELFqbB_0 NDFqbB_0 BNDFqbB_0 COVFqbB_0 XFnqbB_0 BFbqbB_0 FPFqbB_0 FXFqbB_0 FPARqbB_0
             Hc1qbB_0 HmcqbB_0 HtybqbB_0 HxcqbB_0 WCUqbB_0 SELUqbB_0 NDUqbB_0 BNDUqbB_0 COVUqbB_0 W9qbB_0 D9qbB_0 XB9qbB_0 sFqbB ENT9qbB_0 SID9qbB_0 G110qbB_0 D9qbB CertFqbB_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
Qed.

Theorem sec_tail_0hb : ltac2:(tb__ "0|8|
S37OF_;S15S2aS8S8S27Q40M0A1M1S0G1A1M2S16S45VW;Vst;A2S2bR7A1S3bS1fRaS3aR8A1A3S7S1bG1S9R8R1A2S9R9R1A2A3Fi;S7S1bS0S27Q8A1M3A1ScR9R1A2ScRaR1A2A3Fl;S2cVCST;VXGL;RcRcSaRaA1SaR9A1A6S20S23S2S18S17RdA1A2A1S19RdA1A2S1S6S6A2M4S32G4R1S42R9A1A3S40R2S3S6S6S28G0RcA2M5S44S28G0S9RdPcA2A2A1M6A4A2F_;Fbn;S6S1cS20S3fG5A1M7R1A2S24R1S21G7S22G6Z8A2A2A2A2S1dS1bS5G3A1SaReS29G0R2A2A2S4G3A1A3A1F_;Fz;S8G2S36S1fR13S39S1fS2dU0Vst;S2fS26S15R1LX;RcA2R12R11RfReA8S4cR2R1A5S3dS1fS38R10RdS49VCST;VXGL;VW;Vst;R12R11A6A5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 G2. exact (sec_tail_0hb_P ok A Kc rho0 rho a tp0 G2 (PFc CST XGL W st A Kc) (or_intror (or_introl eq_refl))).
Qed.
End INST.
End SpineCallocSec6J.

(* [comment removed for export] *)
Module SpineCallocSec6JW1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "list"; "prod"; "length"; "pair"; "None"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "sobj"; "rl"; "sv"; "holds"; "sprop"; "SVar"; "eval"; "obj_range"; "SAlu"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "DG"; "aa_sec"; "sec_chunk"; "aa_Km"; "aa_ptr_committed"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "div"; "of_nat"; "lt"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS"; "AXK"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "JGs"; "range_noband"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IW1"; "nx0"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump"; "bumpP"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv"; "bumpV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "JLc_ok"; "Lc_ok"; "PFc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "V_NRES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineCallocSec5IW1"; "C5ac"; "C5bc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.SpineCallocSec6IW1"; "FXPa"; "FXPb"; "PXa"; "PXb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec7"; "bx_ok"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2"; "IMG_S"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec4IW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ch.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec4IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CertCallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cc.SpineCallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineCallocSec5IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.SpineCallocSec6IW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.GS nx0.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S6S41VCST;R1A2S41S53R2A2S1eF_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S6S41VCST;R1A2S41S54R2A2S1eF_;F_;Fa;").

Lemma PXnba_0 : ltac2:(tb__ "0|2|
S16S15S2aS8S27Q40A1M0S8S0G0A1S0S35A1S34S2dU1Vst;S2fS26S15S33R1A1LX;R9A2R8R7R6R5R4R3R2R1AcS30SfSeR5A1S4dA3S0SbA1S1bS0S1S1SdSdA2SdA2M1A1S31SbG1S43R1A4S31SbG1S43S4fA4A3S30SbSbS2eS12R9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FG2;").
Proof.
  intros G2 A Kc rho a r tp tr md HJ HF.
  exact (pxa_noband 1%nat st tmax nx0 Hnx_0 (AXK (fun X : AA => bumpP X) G2) A Kc rho a r tp tr md (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HF).
Qed.
Lemma BXoka_0 : ltac2:(tb__ "0|0|
S16S51S26S15S33R1A1LX;R1A2A1FG2;").
Proof. intros G2 X. repeat split; reflexivity. Qed.
Lemma HPATHa_0 : ltac2:(tb__ "0|6|
S16S15S2aS8S27Q40M0A1M1S8S0G1A1S0S35A1S34S2dU1Vst;S2fS26S15S33R1A1LX;M2R9A2R8R7R6R5R4R3R2R1AcS30SfSeR5A1S4dA3S26G2RbS46RaS28G0S9R8PcA2A2A2A3S15S1cS1cS20Z8M3Z20000M4A2S20G4G4A2A2S1cS20S21S25G3S23S2S18S17RbA1A2A1A2G4A2S1aR1A1M5A2S1bG1S11R7S13S52S10S4aA1S14Z4000A1A3A2S29G0S22G5G3A2A2A3A2A2TAs;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FG2;").
Proof.
  intros G2 A Kc rho a r tp tr md HJ HF.
  exact (hpath_a 1%nat st tmax nx0 Hnx_0 (AXK (fun X : AA => bumpP X) G2) A Kc rho a r tp tr md (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HF).
Qed.

Theorem sec_tail_0ha_P : ltac2:(tb__ "0|9|
S37OF_;S15S2aS8S8S27Q40M0A1M1S0G1A1M2S16S0S1S3cS3eA2M3A1S32G3S3S3cS3eS48VW;Vst;A2S47VCST;VXGL;R8R7A4A4R1A3S45VW;Vst;A2S2bR9A1S3bS1fRcS3aRaA1A3S7S1bG1S9RaR1A2S9RbR1A2A3Fi;S7S1bS0S27Q8A1M4A1ScRbR1A2ScRcR1A2A3Fl;S2cVCST;VXGL;ReReSaRcA1SaRbA1A6S20S23S2S18S17RfA1A2A1S19RfA1A2S1S6S6A2M5S32G5R1S42RbA1A3S40R2S3S6S6S28G0ReA2M6S44S28G0S9RfPcA2A2A1M7A4A2F_;Fbn;S6S1cS20S3fG6A1M8R1A2S24R1S21G8S22G7Z8A2A2A2A2S1dS1bS5G4A1SaR10S29G0R2A2A2S4G4A1A3A1F_;Fz;S8G2S36S1fR15S39S1fS2dU1Vst;S2fS26S15S33R1A1LX;ReA2R14R13R11R10A8S4bR2R1A5S3dS1fS38R12RfRdA5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 G2 Posts HPin HUS HKc Hokl HLw HLl HKEPT HL9 HDB RUNDEF.
  set (BX := AXK (fun X : AA => bumpP X) G2). set (Q := LQPA segsA NF rho0 tp0 Posts).
  assert (HW : stopJ_w W st) by (hw_discharge).
  assert (BXg : forall X, aa_geom (BX X) = aa_geom X) by (intros X; reflexivity).
  apply (sec_g43 1%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXa FXPa (PXnba_0 G2) C5ac C5Aa C5Ba Y6Aa Y6Ba E6a CT6a CO6a T6a s6Aa s6Ba s6a R6a
           HC5Aa_0 HC5Ba_0 FBAa_0 FBBa_0 Cert6Aa_0 Cert6Ba_0 E6Aa_0 I6Aa_0 E6Ba_0 I6Ba_0
           WC6a_0 DF6a_0 NX6a_0 HC6a_0 SK6a_0 FC6a_0 FX6a_0 XC6a_0 HCO6a_0 WCO6a_0 He6a_0 Hchk6a_0 HT6a_0 FBC6a_0 FBT6a_0 NXC6a_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY6 tY6. rewrite HD6a_0.
  apply (sec_g44 1%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXa FXPa (PXnba_0 G2) D6a U7a ET7a CT7a CO7a CR7a CS7a CM7a T7a s7a R7a n7a
           WU7a_0 DU7a_0 NXU7a_0 HU7a_0 Cert7a_0 WC7a_0 DF7a_0 NX7a_0 HC7a_0 SK7a_0 FC7a_0 FX7a_0 XC7a_0 HCO7a_0 WCO7a_0
           RB7a_0 HCR7a_0 LEN7a_0 PERM_nd7a_0 PERM_lt7a_0 PERM_cov7a_0 HCS7a_0 MRG7a_0 HCM7a_0 He7a_0 Hchk7a_0 HT7a_0 FBC7a_0 FBT7a_0 NXC7a_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY7 tY7. rewrite HD7a_0.
  apply (sec_g45 1%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXa FXPa (PXnba_0 G2) D7a U8a ET8a CT8a CO8a T8a s8a R8a
           WU8a_0 DU8a_0 NXU8a_0 HU8a_0 Cert8a_0 WC8a_0 DF8a_0 NX8a_0 HC8a_0 SK8a_0 FC8a_0 FX8a_0 XC8a_0 HCO8a_0 WCO8a_0
           He8a_0 Hchk8a_0 HT8a_0 FBC8a_0 FBT8a_0 NXC8a_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY8 tY8. rewrite HD8a_0.
  apply (sec_g46 1%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXa FXPa (PXnba_0 G2) D8a U9a E9fa E9pa CO9pa E9qa
           WU9a_0 DU9a_0 NXU9a_0 HU9a_0 Cert9a_0 SK9a_0 FC9a_0 FX9a_0 FP9a_0 XC9a_0 HCO9a_0 WCO9a_0 Cert9qa_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  - intros rY9 tY9.
    apply (sec_g47d 1%nat st tmax nx0 Hnx_0 BX E9fa S9afa S9bfa D9fa iMfa perm9fa HS9afa_0 HS9bfa_0 HD9fa_0 NDpfa_0 BNDpfa_0 COVpfa_0 BXg D9faA D9faB HD9Afa_0 HD9Bfa_0 FBA9fa_0 FBB9fa_0 ok A Kc rho a Q).
    + intros rZ tZ.
      exact (sec_g48_P 1%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXoka_0 G2) 131072 DZero (SAlu ALU_ADD (SVar V_NRES) (SLit 16384)) FXPa ltac:(first [left; reflexivity | right; reflexivity]) (HPATHa_0 G2)
             false FFfaA swcfaA c1faA c2faA c4faA c5faA mcfaA xcfaA tybfaA SELFfaA_0 NDFfaA_0 BNDFfaA_0 COVFfaA_0 XFnfaA_0 BFbfaA_0 FPFfaA_0 FXFfaA_0 FPARfaA_0
             Hc1faA_0 HmcfaA_0 HtybfaA_0 HxcfaA_0 WCUfaA_0 SELUfaA_0 NDUfaA_0 BNDUfaA_0 COVUfaA_0 W9faA_0 D9faA_0 XB9faA_0 sFfaA ENT9faA_0 SID9faA_0 G110faA_0 D9faA CertFfaA_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
    + intros rZ tZ.
      exact (sec_g48_P 1%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXoka_0 G2) 131072 DZero (SAlu ALU_ADD (SVar V_NRES) (SLit 16384)) FXPa ltac:(first [left; reflexivity | right; reflexivity]) (HPATHa_0 G2)
             false FFfaB swcfaB c1faB c2faB c4faB c5faB mcfaB xcfaB tybfaB SELFfaB_0 NDFfaB_0 BNDFfaB_0 COVFfaB_0 XFnfaB_0 BFbfaB_0 FPFfaB_0 FXFfaB_0 FPARfaB_0
             Hc1faB_0 HmcfaB_0 HtybfaB_0 HxcfaB_0 WCUfaB_0 SELUfaB_0 NDUfaB_0 BNDUfaB_0 COVUfaB_0 W9faB_0 D9faB_0 XB9faB_0 sFfaB ENT9faB_0 SID9faB_0 G110faB_0 D9faB CertFfaB_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
  - intros rY9 tY9.
    apply (sec_g47d 1%nat st tmax nx0 Hnx_0 BX E9qa S9aqa S9bqa D9qa iMqa perm9qa HS9aqa_0 HS9bqa_0 HD9qa_0 NDpqa_0 BNDpqa_0 COVpqa_0 BXg D9qaA D9qaB HD9Aqa_0 HD9Bqa_0 FBA9qa_0 FBB9qa_0 ok A Kc rho a Q).
    + intros rZ tZ.
      exact (sec_g48_P 1%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXoka_0 G2) 131072 DZero (SAlu ALU_ADD (SVar V_NRES) (SLit 16384)) FXPa ltac:(first [left; reflexivity | right; reflexivity]) (HPATHa_0 G2)
             true FFqaA swcqaA c1qaA c2qaA c4qaA c5qaA mcqaA xcqaA tybqaA SELFqaA_0 NDFqaA_0 BNDFqaA_0 COVFqaA_0 XFnqaA_0 BFbqaA_0 FPFqaA_0 FXFqaA_0 FPARqaA_0
             Hc1qaA_0 HmcqaA_0 HtybqaA_0 HxcqaA_0 WCUqaA_0 SELUqaA_0 NDUqaA_0 BNDUqaA_0 COVUqaA_0 W9qaA_0 D9qaA_0 XB9qaA_0 sFqaA ENT9qaA_0 SID9qaA_0 G110qaA_0 D9qaA CertFqaA_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
    + intros rZ tZ.
      exact (sec_g48_P 1%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXoka_0 G2) 131072 DZero (SAlu ALU_ADD (SVar V_NRES) (SLit 16384)) FXPa ltac:(first [left; reflexivity | right; reflexivity]) (HPATHa_0 G2)
             true FFqaB swcqaB c1qaB c2qaB c4qaB c5qaB mcqaB xcqaB tybqaB SELFqaB_0 NDFqaB_0 BNDFqaB_0 COVFqaB_0 XFnqaB_0 BFbqaB_0 FPFqaB_0 FXFqaB_0 FPARqaB_0
             Hc1qaB_0 HmcqaB_0 HtybqaB_0 HxcqaB_0 WCUqaB_0 SELUqaB_0 NDUqaB_0 BNDUqaB_0 COVUqaB_0 W9qaB_0 D9qaB_0 XB9qaB_0 sFqaB ENT9qaB_0 SID9qaB_0 G110qaB_0 D9qaB CertFqaB_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
Qed.

Theorem sec_tail_1ha : ltac2:(tb__ "0|8|
S37OF_;S15S2aS8S8S27Q40M0A1M1S0G1A1M2S16S45VW;Vst;A2S2bR7A1S3bS1fRaS3aR8A1A3S7S1bG1S9R8R1A2S9R9R1A2A3Fi;S7S1bS0S27Q8A1M3A1ScR9R1A2ScRaR1A2A3Fl;S2cVCST;VXGL;RcRcSaRaA1SaR9A1A6S20S23S2S18S17RdA1A2A1S19RdA1A2S1S6S6A2M4S32G4R1S42R9A1A3S40R2S3S6S6S28G0RcA2M5S44S28G0S9RdPcA2A2A1M6A4A2F_;Fbn;S6S1cS20S3fG5A1M7R1A2S24R1S21G7S22G6Z8A2A2A2A2S1dS1bS5G3A1SaReS29G0R2A2A2S4G3A1A3A1F_;Fz;S8G2S36S1fR13S39S1fS2dU1Vst;S2fS26S15S33R1A1LX;RcA2R12R11RfReA8S4bR2R1A5S3dS1fS38R10RdS49VCST;VXGL;VW;Vst;R12R11A6A5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 G2. exact (sec_tail_0ha_P ok A Kc rho0 rho a tp0 G2 (PFc CST XGL W st A Kc) (or_intror (or_introl eq_refl))).
Qed.

Lemma PXnbb_0 : ltac2:(tb__ "0|2|
S16S15S2aS8S27Q40A1M0S8S0G0A1S0S35A1S34S2dU1Vst;S2fS26S15R1LX;R9A2R8R7R6R5R4R3R2R1AcS30SfSeR5A1S4eA3S0SbA1S1bS0S1S1SdSdA2SdA2M1A1S31SbG1S43R1A4S31SbG1S43S50A4A3S30SbSbS2eS12R9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FG2;").
Proof.
  intros G2 A Kc rho a r tp tr md HJ HF.
  exact (pxb_noband 1%nat st tmax nx0 Hnx_0 (AXK (fun X : AA => X) G2) A Kc rho a r tp tr md (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HF).
Qed.
Lemma BXokb_0 : ltac2:(tb__ "0|0|
S16S51S26S15R1LX;R1A2A1FG2;").
Proof. intros G2 X. repeat split; reflexivity. Qed.
Lemma HPATHb_0 : ltac2:(tb__ "0|5|
S16S15S2aS8S27Q40M0A1M1S8S0G1A1S0S35A1S34S2dU1Vst;S2fS26S15R1LX;M2R9A2R8R7R6R5R4R3R2R1AcS30SfSeR5A1S4eA3S26G2RbS46RaS28G0S9R8PcA2A2A2A3S15S1cS1cS20Z8M3G3A2S20G3Z20000A2A2S1cS20S21S25G3S23S2S18S17RbA1A2A1A2G3A2S1aR1A1M4A2S1bG1S11R7S10S4aA1A2S29G0S22G4G3A2A2A3A2A2TAs;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FG2;").
Proof.
  intros G2 A Kc rho a r tp tr md HJ HF.
  exact (hpath_b 1%nat st tmax nx0 Hnx_0 (AXK (fun X : AA => X) G2) A Kc rho a r tp tr md (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HF).
Qed.

Theorem sec_tail_0hb_P : ltac2:(tb__ "0|9|
S37OF_;S15S2aS8S8S27Q40M0A1M1S0G1A1M2S16S0S1S3cS3eA2M3A1S32G3S3S3cS3eS48VW;Vst;A2S47VCST;VXGL;R8R7A4A4R1A3S45VW;Vst;A2S2bR9A1S3bS1fRcS3aRaA1A3S7S1bG1S9RaR1A2S9RbR1A2A3Fi;S7S1bS0S27Q8A1M4A1ScRbR1A2ScRcR1A2A3Fl;S2cVCST;VXGL;ReReSaRcA1SaRbA1A6S20S23S2S18S17RfA1A2A1S19RfA1A2S1S6S6A2M5S32G5R1S42RbA1A3S40R2S3S6S6S28G0ReA2M6S44S28G0S9RfPcA2A2A1M7A4A2F_;Fbn;S6S1cS20S3fG6A1M8R1A2S24R1S21G8S22G7Z8A2A2A2A2S1dS1bS5G4A1SaR10S29G0R2A2A2S4G4A1A3A1F_;Fz;S8G2S36S1fR15S39S1fS2dU1Vst;S2fS26S15R1LX;ReA2R14R13R11R10A8S4cR2R1A5S3dS1fS38R12RfRdA5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 G2 Posts HPin HUS HKc Hokl HLw HLl HKEPT HL9 HDB RUNDEF.
  set (BX := AXK (fun X : AA => X) G2). set (Q := LQPA segsA NF rho0 tp0 Posts).
  assert (HW : stopJ_w W st) by (hw_discharge).
  assert (BXg : forall X, aa_geom (BX X) = aa_geom X) by (intros X; reflexivity).
  apply (sec_g43 1%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXb FXPb (PXnbb_0 G2) C5bc C5Ab C5Bb Y6Ab Y6Bb E6b CT6b CO6b T6b s6Ab s6Bb s6b R6b
           HC5Ab_0 HC5Bb_0 FBAb_0 FBBb_0 Cert6Ab_0 Cert6Bb_0 E6Ab_0 I6Ab_0 E6Bb_0 I6Bb_0
           WC6b_0 DF6b_0 NX6b_0 HC6b_0 SK6b_0 FC6b_0 FX6b_0 XC6b_0 HCO6b_0 WCO6b_0 He6b_0 Hchk6b_0 HT6b_0 FBC6b_0 FBT6b_0 NXC6b_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY6 tY6. rewrite HD6b_0.
  apply (sec_g44 1%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXb FXPb (PXnbb_0 G2) D6b U7b ET7b CT7b CO7b CR7b CS7b CM7b T7b s7b R7b n7b
           WU7b_0 DU7b_0 NXU7b_0 HU7b_0 Cert7b_0 WC7b_0 DF7b_0 NX7b_0 HC7b_0 SK7b_0 FC7b_0 FX7b_0 XC7b_0 HCO7b_0 WCO7b_0
           RB7b_0 HCR7b_0 LEN7b_0 PERM_nd7b_0 PERM_lt7b_0 PERM_cov7b_0 HCS7b_0 MRG7b_0 HCM7b_0 He7b_0 Hchk7b_0 HT7b_0 FBC7b_0 FBT7b_0 NXC7b_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY7 tY7. rewrite HD7b_0.
  apply (sec_g45 1%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXb FXPb (PXnbb_0 G2) D7b U8b ET8b CT8b CO8b T8b s8b R8b
           WU8b_0 DU8b_0 NXU8b_0 HU8b_0 Cert8b_0 WC8b_0 DF8b_0 NX8b_0 HC8b_0 SK8b_0 FC8b_0 FX8b_0 XC8b_0 HCO8b_0 WCO8b_0
           He8b_0 Hchk8b_0 HT8b_0 FBC8b_0 FBT8b_0 NXC8b_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY8 tY8. rewrite HD8b_0.
  apply (sec_g46 1%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXb FXPb (PXnbb_0 G2) D8b U9b E9fb E9pb CO9pb E9qb
           WU9b_0 DU9b_0 NXU9b_0 HU9b_0 Cert9b_0 SK9b_0 FC9b_0 FX9b_0 FP9b_0 XC9b_0 HCO9b_0 WCO9b_0 Cert9qb_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  - intros rY9 tY9.
    apply (sec_g47d 1%nat st tmax nx0 Hnx_0 BX E9fb S9afb S9bfb D9fb iMfb perm9fb HS9afb_0 HS9bfb_0 HD9fb_0 NDpfb_0 BNDpfb_0 COVpfb_0 BXg D9fbA D9fbB HD9Afb_0 HD9Bfb_0 FBA9fb_0 FBB9fb_0 ok A Kc rho a Q).
    + intros rZ tZ.
      exact (sec_g48_P 1%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXokb_0 G2) 8 DUnknown (SVar V_NRES) FXPb ltac:(first [left; reflexivity | right; reflexivity]) (HPATHb_0 G2)
             false FFfbA swcfbA c1fbA c2fbA c4fbA c5fbA mcfbA xcfbA tybfbA SELFfbA_0 NDFfbA_0 BNDFfbA_0 COVFfbA_0 XFnfbA_0 BFbfbA_0 FPFfbA_0 FXFfbA_0 FPARfbA_0
             Hc1fbA_0 HmcfbA_0 HtybfbA_0 HxcfbA_0 WCUfbA_0 SELUfbA_0 NDUfbA_0 BNDUfbA_0 COVUfbA_0 W9fbA_0 D9fbA_0 XB9fbA_0 sFfbA ENT9fbA_0 SID9fbA_0 G110fbA_0 D9fbA CertFfbA_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
    + intros rZ tZ.
      exact (sec_g48_P 1%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXokb_0 G2) 8 DUnknown (SVar V_NRES) FXPb ltac:(first [left; reflexivity | right; reflexivity]) (HPATHb_0 G2)
             false FFfbB swcfbB c1fbB c2fbB c4fbB c5fbB mcfbB xcfbB tybfbB SELFfbB_0 NDFfbB_0 BNDFfbB_0 COVFfbB_0 XFnfbB_0 BFbfbB_0 FPFfbB_0 FXFfbB_0 FPARfbB_0
             Hc1fbB_0 HmcfbB_0 HtybfbB_0 HxcfbB_0 WCUfbB_0 SELUfbB_0 NDUfbB_0 BNDUfbB_0 COVUfbB_0 W9fbB_0 D9fbB_0 XB9fbB_0 sFfbB ENT9fbB_0 SID9fbB_0 G110fbB_0 D9fbB CertFfbB_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
  - intros rY9 tY9.
    apply (sec_g47d 1%nat st tmax nx0 Hnx_0 BX E9qb S9aqb S9bqb D9qb iMqb perm9qb HS9aqb_0 HS9bqb_0 HD9qb_0 NDpqb_0 BNDpqb_0 COVpqb_0 BXg D9qbA D9qbB HD9Aqb_0 HD9Bqb_0 FBA9qb_0 FBB9qb_0 ok A Kc rho a Q).
    + intros rZ tZ.
      exact (sec_g48_P 1%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXokb_0 G2) 8 DUnknown (SVar V_NRES) FXPb ltac:(first [left; reflexivity | right; reflexivity]) (HPATHb_0 G2)
             true FFqbA swcqbA c1qbA c2qbA c4qbA c5qbA mcqbA xcqbA tybqbA SELFqbA_0 NDFqbA_0 BNDFqbA_0 COVFqbA_0 XFnqbA_0 BFbqbA_0 FPFqbA_0 FXFqbA_0 FPARqbA_0
             Hc1qbA_0 HmcqbA_0 HtybqbA_0 HxcqbA_0 WCUqbA_0 SELUqbA_0 NDUqbA_0 BNDUqbA_0 COVUqbA_0 W9qbA_0 D9qbA_0 XB9qbA_0 sFqbA ENT9qbA_0 SID9qbA_0 G110qbA_0 D9qbA CertFqbA_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
    + intros rZ tZ.
      exact (sec_g48_P 1%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXokb_0 G2) 8 DUnknown (SVar V_NRES) FXPb ltac:(first [left; reflexivity | right; reflexivity]) (HPATHb_0 G2)
             true FFqbB swcqbB c1qbB c2qbB c4qbB c5qbB mcqbB xcqbB tybqbB SELFqbB_0 NDFqbB_0 BNDFqbB_0 COVFqbB_0 XFnqbB_0 BFbqbB_0 FPFqbB_0 FXFqbB_0 FPARqbB_0
             Hc1qbB_0 HmcqbB_0 HtybqbB_0 HxcqbB_0 WCUqbB_0 SELUqbB_0 NDUqbB_0 BNDUqbB_0 COVUqbB_0 W9qbB_0 D9qbB_0 XB9qbB_0 sFqbB ENT9qbB_0 SID9qbB_0 G110qbB_0 D9qbB CertFqbB_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
Qed.

Theorem sec_tail_1hb : ltac2:(tb__ "0|8|
S37OF_;S15S2aS8S8S27Q40M0A1M1S0G1A1M2S16S45VW;Vst;A2S2bR7A1S3bS1fRaS3aR8A1A3S7S1bG1S9R8R1A2S9R9R1A2A3Fi;S7S1bS0S27Q8A1M3A1ScR9R1A2ScRaR1A2A3Fl;S2cVCST;VXGL;RcRcSaRaA1SaR9A1A6S20S23S2S18S17RdA1A2A1S19RdA1A2S1S6S6A2M4S32G4R1S42R9A1A3S40R2S3S6S6S28G0RcA2M5S44S28G0S9RdPcA2A2A1M6A4A2F_;Fbn;S6S1cS20S3fG5A1M7R1A2S24R1S21G7S22G6Z8A2A2A2A2S1dS1bS5G3A1SaReS29G0R2A2A2S4G3A1A3A1F_;Fz;S8G2S36S1fR13S39S1fS2dU1Vst;S2fS26S15R1LX;RcA2R12R11RfReA8S4cR2R1A5S3dS1fS38R10RdS49VCST;VXGL;VW;Vst;R12R11A6A5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 G2. exact (sec_tail_0hb_P ok A Kc rho0 rho a tp0 G2 (PFc CST XGL W st A Kc) (or_intror (or_introl eq_refl))).
Qed.
End INST.
End SpineCallocSec6JW1.

(* [comment removed for export] *)
Module F0A_hbN_pure.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "sec_chunk"; "sc_map_beg"; "aa_sec"; "sc_map_size"; "aa_geom"; "AA"; "aa_live"; "ag_pab"; "ag_spacebeg"; "sc_size"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "of_nat"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "nat"; "length"; "list"; "Some"; "bool"; "false"; "option"; "pair"; "prod"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kPtrArrayReserve"; "PG"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "is_primary"; "kQuarantineMax"; "round_up"; "@Stdlib.Lists.List"; "nth_error"; "In"; "@Corelib.Init.Peano"; "le"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_tail"; "CHFh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws"; "N8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue"; "fam_ok"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQS_glue SegQS_scan SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.SegQS_k.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import PaidMunmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.InvQ10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.InvQ11.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma hb_pure : ltac2:(tb__ "0|c|
S2fS30R1A1S9S1eS1eS16S34Q40A1A1S16S2bA1S2aS13S13S31S2cR8R7R5R3A5S32RbR9R7R6R5R4A6S27S1cS13S13A2S1bS13S13R4R3A4SaRaA1A3S10S24R4A2S0S1S18S23R5A1S19A3S2S14S14S2S4S4S0S1S1aS4A1M0S26S4S6ReA1M1R2A3S17S4R1A2M2A3S0S1S13R8SfSfS5R1A1M3S20A2Z800A2A3S0S1S13SdR1A1SfS25R7Z8M4A2Z1000A2A3S0SeZ1R7A2S0SeSfZ1800S2eR7A1A2S7R1A1M5A2S0S2dR1A1S0S3SeSfG3G5A2M6S22A2SeS21G3A2A2S0S3SeSfSbS8ReA1A1M7S1fA2G3A2SeG6G7A2A2S0SeS11G4S12S15S4G1A2A1A2S1fA2S0S2S14S14S0S28R1U2A2S33R1ScS8RfA1A1S5R2A1S7R2A1A4A2Lf;A2S4S1G0S26S4S6RfA1M8S1dS15S4G8A2U1M9A2A3G2A3S29R4S1dS15S4S6R10A1A2G9A2A2S3SeSfS5R3A1MaZ20A2S5R4A1MbA2SeSfGbS7R4A1A2GaA2A2F_;F_;Flst;A2A2A2A2A2A2A2A2A2A2Lch;A2Li;A2A2F_;F_;F_;F_;Fn;Fp;Fmd;Ftr;Ftp;FrK;Frp;FA;F_;FKc;").
Proof.
  intros Kc HKc A rp rK tp tr md p n HA HK0 HL HBIG.
  pose proof (big_not_primary n HBIG) as HPR. split; [exact HPR|].
  destruct (live_big_chunk A rp tp md p n HA HL HPR) as (i & ch & HI & HU & HSZ & HMS & HM1 & HM2 & HM3 & HLO & HHI & HRZ & HN & HFIT & _).
  exists i, ch. pose proof (N8_facts n HN) as (N1 & N2 & N3 & N4).
  destruct (chk_facts (K0 Kc) (K0_sec Kc HKc) A rK tp tr md i ch HK0 HI) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10). cbv zeta in C1, C2, C3, C4, C5, C6, C7, C8, C9, C10.
  destruct (thr_facts (K0 Kc) (K0_laws Kc HKc) A rK tp tr md HK0) as (_ & _ & _ & HSB & _).
  pose proof (ks_repr segsA (K0 Kc) (K0_sec Kc HKc) A rK tp tr md HK0) as (_ & _ & (S2a & S2b) & _).
  unfold kQuarantineMax, PG in *.
  split; [exact HI|]. split; [exact HU|]. split; [exact HSZ|]. split; [exact HN|]. split; [lia|].
  split; [unfold CHFh; repeat split; try assumption; lia|]. split; [exact C6|]. split; [destruct C9; [right | left]; assumption|]. split; [lia|]. split.
  - unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, kSpaceSize in *.
    destruct C6 as [C6|C6]; [exists 0%nat; split; [lia | cbn [fam_ok]; lia]|].
    destruct C7 as [C7|C7]; [exists 1%nat; split; [lia | cbn [fam_ok]; lia] | exists 2%nat; split; [lia | cbn [fam_ok]; lia]].
  - intros lst Hl Hlt.
    destruct (chk_facts (K0 Kc) (K0_sec Kc HKc) A rK tp tr md _ lst HK0 Hl) as (_ & _ & L3 & _). cbv zeta in L3.
    destruct (C10 _ lst Hl ltac:(lia)) as [X|X]; [right; exact X | left; lia].
Qed.
End F0A_hbN_pure.

(* [comment removed for export] *)
Module F0A_hbN_scand.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "nil"; "pair"; "andb"; "bool"; "app"; "prod"; "list"; "length"; "option"; "true"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "sobj"; "SLit"; "ss_objs"; "SPUle"; "SVar"; "SPNot"; "SAlu"; "SPAlign"; "SPBranch"; "SPUlt"; "ss_facts"; "sprop_below"; "sprop_eqb"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "la_state"; "list_eqb"; "sobj_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "add"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue"; "dropN"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states"; "vMS"; "vPTR"; "vCHV"; "vPAB"; "O_chS"; "vIDX"; "vNCH"; "TOPMAX"; "selX"; "sel_last"; "vEND"; "vLAST"; "vLIDX"; "vNEAR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cw.F0A_hbN_scand"; "lastb"; "lfh"; "vNXT"; "F2Xh"; "LT1h"; "LT2h"; "Ld_hb"; "ZULh"; "FCHs"; "LFh"; "Lx_hb"; "M_exit_hb"; "M_first_hb"; "M_loop_hb"; "T_exit_hb"; "T_first_hb"; "T_loop_hb"; "selb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states"; "mT"; "F2_hb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SegQS_loop"; "a3_of"; "EQF"; "NSC"; "BSX"; "F_hX"; "F_lenX"; "NX"; "UX"; "ZDNX"; "ZDU"; "ZUXl"; "hv_of"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert"; "VS0h"; "hf_SC"; "hf_lPL"; "hf_LA"; "hv_SX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.F0A_hbN_zones"; "zd_allb"; "zds_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "O_sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM"; "idm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib"; "mkST"; "s_ok"; "s_okU"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "ALU_SLL"; "BC_EQ"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "apply_axforms"; "@Stdlib.Arith.PeanoNat.Nat"; "ltb"; "eqb"; "even"; "modulo"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "nth"; "seq"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "F_depth"; "Wcan"; "chain_pre"; "free_depth"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQS_glue SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel F0A_blind.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_hbN_env F0A_hbN_cert.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.InvQ10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.SegQS_k OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_blind OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.F0A_hbN_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_hbN_step OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_entry.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition LT1h : sprop := SPBranch BC_LTU mT vCHV.
Definition LT2h : sprop := ltac2:(tb__ "0|0|
S17S68S15S65S49S2bA3S15S65S49S36A3A3").
Definition LFh (k : nat) : list sprop := ltac2:(tb__ "0|2|
S0SdS5SdL_;M0S6eVk;A1S4cS14S4cA1X5x2S0SdG0S6cS6fVk;U4M1A2U2A2S3bS14S3bA1X5x2S0SdG0S6cVk;G1A2S3cS14S3cA1X5x2S2SdA1A3A3A3").

Definition ZULh : list nat := ltac2:(tb__ "0|0|
S0S1U0S0S1U1S0S1U2S0S1U3S0S1U4S0S1U5S0S1U9S2S1A1A3A3A3A3A3A3A3").
Definition vNXT : positive := 209%positive.
Definition M_first_hb : vmap := ltac2:(tb__ "0|2|
S6S7S1cSeA2M0S60S58A1S0G0S3S1cSePd2S2cA4S0G0S3S1cSePd3M1S13G1A1A4S0G0S3S1cSePd4S10Z0A1A4S0G0S3S1cSePd5S24S2cS15S66S2fS10Z3A1A3A2A4S2G0A1A3A3A3A3A3").
Definition T_first_hb (nW : nat) (LA SC : axst) : strans := ltac2:(tb__ "0|4|
S61VLA;U0M0S4dS2cS13Pd3M1A1A2S0S1cG1S2S1cA1A3S2SdA1VSC;S43S5eVnW;S11S1eS26VLA;G0A2A1A1A2S0S7S7S1S1dA2M2S1dA2M3S3G2S1dS3S1S1dU9Z0A4Z8A4S2G3A1A3A9").
Definition M_loop_hb (k : nat) : vmap := ltac2:(tb__ "0|1|
S6S7S1cSeA2M0S60S58A1S0G0S3S1cSePd2S24S2aS10Z8A1A2A4S0G0S3S1cSePd3S13S39A1A4S0G0S3S1cSePd4S4bVk;A1A4S0G0S3S1cSePd5S33A4S2G0A1A3A3A3A3A3").
Definition T_loop_hb (nW : nat) (L SC : axst) (k : nat) : strans := ltac2:(tb__ "0|4|
S61VL;U1M0S4dS24S2aS10Z8M1A1A2S13S39A1A2S0S1cS39S2S1cA1A3S2SdA1VSC;S44Vk;A1S5eVnW;S11S1eS26VL;G0A2A1A1A2S0S7S7S1S1dA2M2S1dA2M3S3G2S1dS3S1S1dU9Z0A4G1A4S2G3A1A3A9").

Definition F2Xh (f : nat) (l : bool) (hv : positive) : list sprop := ltac2:(tb__ "0|4|
S13Vhv;A1SeS6SdS0SdS50R1A1S0SdS14S17S67R1S10Z0A1A3A1S0SdS12R1S49A2S0SdS18S49S24R1S29A2M0A2S0SdS16Vhv;ZcM1A2S0SdS16PcbG1A2S0SdS12S10Z12000A1S29A2S0SdS12S29S10S30A1M2A2S0SdS12S10Z646000A1R1A2S0SdS12G0G2A2S0SdS12S24S29R1A2G2A2S2SdA1M3A3A3A3A3A3A3A3A3A3A3A3S6SdS4fVf;R1A2S5S8SdA1Ll;Vl;G3S0SdS18S2eS24S2fS10N1A1A2A2G3A3X5x2A3A3ThT;").
Lemma F2Xh_F2 : ltac2:(tb__ "0|0|
S1S5S57S8SdA1S3aR2R1PcaA3S4aR2R1A2A3Fl;Ff;"). Proof. intros [|[|f]] [|]; reflexivity. Qed.
Definition M_exit_hb (k : nat) (l : bool) : vmap := ltac2:(tb__ "0|2|
S6S7S1cSeA2M0S60S58A1S6G0S0G0S3S1cSePcaS4bVk;A1A4S0G0S3S1cSePcbS29A4S2G0A1M1A3A3S5S8G0A1Ll;Vl;G1S0G0S3S1cSePccS2eA4S0G0S3S1cSePcdS34A4S0G0S3S1cSePceS35A4G1A3A3A3X5x2A3A3").
Definition Lx_hb (L : axst) : axst := ltac2:(tb__ "0|0|
S31VL;S0SfS5fS2SfA1A3A2").
Definition Ld_hb (L : axst) : axst := dropk (Lx_hb L) 1.
Definition T_exit_hb (nW : nat) (L SX : axst) (f k : nat) (l : bool) : strans := ltac2:(tb__ "0|2|
S61S3dVL;A1M0U1M1S51Vl;S4bVk;A1A2S4eVl;A1S3aVf;Vl;S56Vk;A1A3VSX;S42Vk;Vl;A2S5eVnW;S11S1eS26G0G1A2A1A1A2S53Vl;A1A9").

Definition lastb (objs : list sobj) (o : sobj) : bool := ltac2:(tb__ "0|0|
S22SfS23S74SfS64S9SfVobjs;A2U1A2Vobjs;A3S0SfVo;S2SfA1A3A4").
Lemma lastb_sound : ltac2:(tb__ "0|1|
S8SfA1M0SfS57S5S37R2R1A2SbA3S57G0R3S6SfS70SfS64S9SfR3A2U1A2R3A3S0SfR2S2SfA1A3A3A3F_;Fo;Fobjs;").
Proof. intros objs o H. unfold lastb in H. apply (list_eqb_sound sobj_eqb sobj_eqb_sound) in H. rewrite <- H. symmetry. apply firstn_skipn. Qed.

Definition lfh (cf : hbfam) (k : nat) : axst := ltac2:(tb__ "0|0|
S72S1fVk;S71S20S1fS21S5aVcf;A1A4S59Vcf;A1A4").
Definition FCHs (nW : nat) : list sprop := ltac2:(tb__ "0|0|
S6SdS77S76VnW;A1A1S75S78A1A3").
Definition scanF_chk (nW : nat) (cf : hbfam) : bool := ltac2:(tb__ "0|8|
S4S4S4S4S4S4S6dS9S20S5aVcf;A1A2U8M0A2S62S46VnW;S5bVcf;A1M1S59Vcf;A1M2A3A1A2S5dVnW;S3eS11S1eS26G1U0M3A2A1A1A3A2S27SdSdS28SdS1bR1A1M4S19S1eG1A1A1A3Lg;S3fVnW;A1M5A3A2S27SdS1aS25A1G5A3A2S27S1S1S4S4S62S47VnW;S38Vcf;R1A2M6G2R1A4A1S5dVnW;S3eS11S1eS26G6U1M7A2A1A1A3A2S37S11S1eG6A1A1S2dS2aS2bA2A2A2Lk;S0S1G7S0S1U3S0S1U5S0S1U7S2S1A1A3A3A3A3A3A2S27S1S1S27SdSdS28SdG4S19S1eS38Vcf;R2A2A1A1A3LF;S40R1A1A3Lk;S73G3G0A2A3A2").
Definition selb (L : axst) : bool := ltac2:(tb__ "0|0|
SaS1fA1S5Lx;S6bVL;S0S69S6aS32VL;S0SfS5fS2SfA1A3A2A1S2S69A1A3A2S1fSbLa;ScXax2").
Definition scanV_chk (nW : nat) (cf : hbfam) (f : nat) (l : bool) (cv : hbvar) : bool := ltac2:(tb__ "0|1|
S27S1S1S38Vcf;R1A2S1fS4S4S4S4S48R1A1S37S11S1eS41R1A1A1A1S5fA2A2S37S11S1eS3dR1A1M0A1A1S2dS2aS2bA2A2A2S63S45VnW;R1S5cVcv;A1Vf;R2Vl;A6S52S4bR2A1A1S54A3A2S5dVnW;S55Vl;A1S11S1eS26G0U1A2A1A1A3A2TL;Lk;S0S1U0S0S1U2S0S1U4S0S1U6S2S1A1A3A3A3A3A3").

Record hbscanF_ok (nW : nat) (cf : hbfam) : Prop := mkSCF { sf_chk : scanF_chk nW cf = true }.
Record hbscanV_ok (nW : nat) (cf : hbfam) (f : nat) (l : bool) (cv : hbvar) : Prop := mkSCV { sv_chk : scanV_chk nW cf f l cv = true }.
End F0A_hbN_scand.

(* [comment removed for export] *)
Module F0A_hbN_du.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "rw"; "SLit"; "cell"; "DUnknown"; "mkCell"; "mkObj"; "valuation"; "odefault"; "SAlu"; "ob_dflt"; "obj_range"; "sv"; "tfact"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "or"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "of_nat"; "div"; "sub"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "false"; "true"; "list"; "length"; "Some"; "nil"; "option"; "andb"; "app"; "fst"; "nat"; "pair"; "prod"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "sec_chunk"; "aa_sec"; "sc_map_beg"; "ag_spacebeg"; "sc_map_size"; "aa_geom"; "ag_ctx"; "ag_thread"; "sc_size"; "topG"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert"; "hv_DUo"; "hbvar_ok"; "hv_EUd"; "hv_EUx"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws"; "N8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "kPtrArrayReserve"; "PG"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kSpaceSize"; "round_up"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue"; "same_rng"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states"; "vLAST"; "vIDX"; "vNCH"; "vPAB"; "vH"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cw.F0A_hbN_du"; "DUCh"; "du_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cw.F0A_hbN_du.Du"; "DUPIN"; "NUMSh"; "CLZh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states"; "D_U_hb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_unmap"; "DUZh"; "JPh"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "sobj_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_blind"; "JW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_env"; "hbenv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4"; "chunk_sh_zone"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQS_glue SegQS_scan SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.SegQS_k.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import PaidMunmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SysCallA MmapA MmapFixedA MmapNodesA MunmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require PaidMunmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel F0A_blind.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_hbN_cert.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_hbN_env.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PaidMunmap OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.InvQ10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_blind OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_hbN_step OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_unmap OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.InvQ11.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition DUCh (l : bool) : list sobj := ltac2:(tb__ "0|b|
S27S0S1dS0S6S2Z0A1M0S2Zede10A1M1S2Zede18A1S1dS3S5G1Z8M2S49S4dS2N1A1A2A3S24S3A1M3A3S4A5S1dS0S6G0S2Zee040A1M4S2Zee044A1S1dS3S5G4Z1G0A3S1dS3S5S2Zee041A1Z3M5G0A3G3A3A3S4A5S24S0A1M6A3A3S1eS21S0A1Ll;Vl;S1dS0S6S49S9S50S4dS2G5A1M7A3S4eA2M8S2N8A1M9G0S1dS3S5S2Zfffffffffffffff8A1G2S4fA3G3A3S4A5G6A3S1dS0S6S49S4eS9S50S4cG7A3A2G0S2G2A1S1dS3S5G0G2S4bA3G3A3S4A5S1dS0S6G8G9G0S1dS3S5G9G2S4bA3G3A3S4A5S1dS0S6S4bS2Z18A1MaS2Z20A1S1dS3S5GaG2S4cA3G3A3S4A5G6A3A3A3X1ex2A3").
Definition du_chk (l : bool) (cv : hbvar) : bool := ltac2:(tb__ "0|2|
S26S39S0S0S38S0S5cR1A1S3bVcv;A1M0A3Lo;S52Vl;A1A3S39S0S0S8S1eLx;SaR1A1S20S1fS1fS1cS1fLl0;M1G1S1bScS21S2bS1bS1bA2A1S21SdA1S1fLtmpl;Lflds;Lcnt;Lesz;X8x6Lo;G0A3A2").

Lemma existsb_same_In : ltac2:(tb__ "0|0|
S0S21S0A1SfS1eS38S0S4aR2A1R1A3S20A3S10S0S0SeS37S0R1R3A3SfS1eS4aR4R1A2S20A3A2Lq;A2F_;FL;Fo;").
Proof. intros o L H. apply existsb_exists in H. exact H. Qed.

Section Du.
Variables (nW : nat) (Kc : KcA).
Hypothesis HKc : Kc_ok Kc.
Variables (A : AA) (rho1 : valuation) (p n : Z) (i : nat) (ch lst : sec_chunk) (l : bool) (TZ : Z -> Prop).
Let h : Z := sc_map_beg ch.
Let msz : Z := sc_map_size ch.
Let G : ageom := aa_geom A.
Let PAB : Z := ag_pab G.
Let NC : Z := Z.of_nat (length (aa_sec A)).
Hypothesis HI : ltac2:(tb__ "0|0|
SfS25S2dA1S3aS2dS2eVA;A1Vi;A3S23S2dVch;A2A3").
Hypothesis HU : ltac2:(tb__ "0|0|
SfS1bVp;S13S13S2fVch;A1S44A2Z800A2A3").
Hypothesis HSZ : ltac2:(tb__ "0|0|
SfS1bS35Vch;A1S13S48Vn;Z8A2Z1000A2A3").
Hypothesis HN : 1 <= n.
Hypothesis HNB : ltac2:(tb__ "0|0|
S12S13Z1800S41Vn;A1A2S31Vch;A1A2").
Hypothesis Hl : ltac2:(tb__ "0|1|
SfS25S2dA1S3aS2dS2eVA;A1M0S3fS22S2dG0A2U1A2A3S23S2dVlst;A2A3").
Hypothesis HLT : ltac2:(tb__ "0|0|
SfS1eVl;S20A3SfS29Vi;S3fS22S2dS2eVA;A1A2U1A2A3F_;").
Hypothesis HLF : ltac2:(tb__ "0|0|
SfS1eVl;S1fA3S5aVi;S3fS22S2dS2eVA;A1A2U1A2A2F_;").
Hypothesis HPIN : ltac2:(tb__ "0|4|
SeSfS1aQ40M0A1M1S1Vrho1;P97A2S19G0S34S32VA;A1M2A1A2A3SeSfG1S1Vrho1;P98A2S19G0S33G2A1A2A3SeSfG1S1Vrho1;P9bA2S19G0S30G2A1A2A3SeSfG1S1Vrho1;PcA2S19G0Vp;A2A3SeSfG1S1Vrho1;P69A2S19G0S41Vn;A1M3A2A3SfG1S1Vrho1;P6aA2S19G0S17G3Z8A2A2A3A2A2A2A2A2").

Hypothesis HZT : ltac2:(tb__ "0|0|
S1bS58VA;Vi;Vch;R1A4VTZ;R2A1F_;Fz;").
Hypothesis HZTt : ltac2:(tb__ "0|0|
S1bSeS12VPAB;R1A2S14R1S13VPAB;S43A2A2A2VTZ;R2A1F_;Fz;").
Let JH : jpredA := ltac2:(tb__ "0|0|
S5dS40S61Vch;A1VTZ;S5fVnW;S60S1fVA;VKc;Vrho1;A6A4").
Let JP : jpredA := ltac2:(tb__ "0|0|
S59VnW;VKc;VA;Vrho1;Vi;Vch;Vlst;Vl;VTZ;A9").
Variables (SC : axst) (f : nat) (cv : hbvar).
Hypothesis VOK : ltac2:(tb__ "0|0|
S3cVSC;Vf;Vl;Vcv;A4").
Hypothesis DUOK : ltac2:(tb__ "0|0|
SfS1eS53Vl;Vcv;A2S20A3").

Definition DUPIN (r : valuation) : Prop := ltac2:(tb__ "0|2|
SeSfS1aQ40M0A1M1S1Vr;Pc8A2S19G0VPAB;A2A3SeSfG1S1Vr;Pc9A2S19G0VNC;A2A3SeSfG1S1Vr;Pc3A2S19G0S13S30VG;A1S47A2A2A3SeSfG1S1Vr;PcaA2S19G0Vh;A2A3SeSfG1S1Vr;PcbA2S19G0Vmsz;A2A3SfS1eVl;S1fA3SeSfG1S1Vr;PccA2S19G0S16Vi;A1A2A3SfG1S1Vr;PcdA2S19G0S2fVlst;A1A2A3A2F_;A2A2A2A2A2").

Definition CLZh (z : Z) : Prop := ltac2:(tb__ "0|1|
SeS12S13VPAB;S15Z8M0S18VNC;Z1A2A2A2Vz;A2S14Vz;S13VPAB;S15G0VNC;A2A2A2A2").

Definition NUMSh : Prop := ltac2:(tb__ "0|5|
SeS12S42VPAB;A2SeS12S13VPAB;S43A2M0S36VG;A1M1A2SeS12Z1VNC;A2SeS12S15Z8VNC;A2S43A2SeS14S16Vi;A1VNC;A2SeS12S42S2fVlst;A1M2A2SeS12S13G2S31Vlst;A1M3A2G1A2SeS12Z12000M4G3A2SeS12S42Vh;A2SeS12S13Vh;Vmsz;A2G1A2SeS12G4Vmsz;A2SeS12Z10Vp;A2S11S12G0S46A2S12S45VPAB;A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Lemma nums_of_env : ltac2:(tb__ "0|0|
S7S5eVA;S2aS1bS1bVp;Vn;A4Vi;Vch;R1A5S55F_;Fr;").
Proof.
  intros r QS. pose proof (qs_chunk A (p, n) i ch r QS) as (_ & _ & MS & IH & HT & _).
  destruct QS as [HG HSEP3 _ _ HSR _ _ _ HSEP _ _ _ _].
  pose proof HSR as (SC1 & _ & (B1 & B2) & _ & PD & _). pose proof (dyn_ok_big _ _ _ PD ltac:(unfold kPtrArrayReserve; lia)) as BIG.
  destruct PD as (_ & _ & _ & P3 & _ & P5).
  pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite HI; discriminate)) as LTi.
  destruct (SC1 _ lst Hl) as (_ & _ & _ & _ & _ & _ & _ & L8 & L9 & L10 & L11 & L12 & _).
  pose proof (dyn_in_big _ _ _ L10) as LBIG.
  assert (LMS : 73728 <= sc_map_size lst).
  { rewrite L11. unfold round_up, PG in *. pose proof (Z.div_mod (sc_size lst + (4096 - 1)) 4096 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (sc_size lst + (4096 - 1)) 4096 ltac:(lia)). nia. }
  unfold NUMSh, NC, PAB, G, h, msz, IMG_HI, PG in *. cbn [fst snd] in *. repeat split; try assumption; lia.
Qed.

Lemma DUp_ranges : ltac2:(tb__ "0|3|
S7S0S55S54R3A1SfS1aQ40M0A1M1S1R4PcA2S19G0Vp;A2A3SfG1S1R5P69A2S19G0S41Vn;A1A2A3S37S0R5S57Vl;A1A3S1bSeS12S28S1bS1bSbR8R7A2M2A3R1A2S14R1S2cS1bS1bG2A3A2A2S11S58VA;Vi;Vch;R2A4SeSfS1eVl;S1fA3S56R2A1A2A2F_;Fz;F_;F_;F_;F_;F_;Fq;Fr;").
Proof.
  intros r q NM (E200 & E201 & _ & EH & E203 & XF) E12 E105 Hin z Hz.
  unfold NUMSh in NM. destruct NM as (P0 & P1 & N1 & N8' & LTi & L0 & L1 & L2 & H0 & H1 & H2 & PP & _).
  pose proof (topG_range G) as TG. pose proof (N8_facts n HN) as (X1 & X2 & X3 & X4). unfold IMG_HI, kPtrArrayReserve, PG in *. fold h msz in HNB, HU.
  assert (EvH : bv_unsigned (eval r vH) = h) by (unfold vH; cbn [eval]; rewrite EH, u64_lit by lia; reflexivity).
  assert (EPb : eval r vPAB = Z_to_bv 64 PAB) by (unfold vPAB; cbn [eval]; exact E200).
  assert (ENc : eval r vNCH = Z_to_bv 64 NC) by (unfold vNCH; cbn [eval]; exact E201).
  assert (EvCL : bv_unsigned (eval r (add (SAlu ALU_SLL vNCH (SLit 3)) vPAB)) = 8 * NC + PAB).
  { rewrite (eval_add_z r _ vPAB (8 * NC) PAB (eval_sll3 r vNCH NC ENc ltac:(lia)) EPb) by lia. rewrite u64_lit by lia. reflexivity. }
  assert (Ev12 : bv_unsigned (eval r (SVar 12)) = p) by (cbn [eval]; rewrite E12, u64_lit by lia; reflexivity).
  assert (RB : obj_range r O_blkN = (p, p + N8 n)).
  { unfold O_blkN, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite Ev12, soff_lit_small by lia.
    rewrite (soff_of_val r vN8 (N8 n)) by (first [unfold vN8; cbn [eval]; rewrite E105, u64_lit by lia; reflexivity | lia]). f_equal; lia. }
  unfold DUZh, CLZh, chunk_zone, sec_junk_zone, sec_tbl_zone, SEC_INST. fold h msz G PAB NC.
  unfold D_U_hb in Hin. apply in_app_or in Hin as [Hin|Hin].
  - cbn [In] in Hin. repeat (destruct Hin as [<-|Hin]); [| | | | | | | | | destruct Hin];
      try (rewrite RB in Hz; cbn [fst snd] in Hz; left; left; lia);
      unfold O_secn, O_secs, O_secm, O_secg, O_hh, O_hidx, O_clast, O_hdr, carved, SEC_INST in Hz; rewrite obj_range_mk in Hz by lia; rewrite ?EvH, ?EvCL, ?Ev12 in Hz; cbn [fst snd eval] in Hz; rewrite ?u64_lit in Hz by lia.
    + left. right. right. right. left. lia.
    + left. right. right. left. left. lia.
    + left. right. right. right. right. left. lia.
    + left. right. right. left. right. lia.
    + left. left. lia.
    + left. left. lia.
    + destruct l.
      * pose proof (HLT eq_refl) as EI. left. right. right. right. right. right. left. unfold NC in *. lia.
      * right. split; [reflexivity | lia].
    + left. left. lia.
  - destruct l; [destruct Hin|]. destruct (XF eq_refl) as (E204 & E205).
    assert (EvCI : bv_unsigned (eval r (add vPAB (SAlu ALU_SLL vIDX (SLit 3)))) = PAB + 8 * Z.of_nat i).
    { rewrite (eval_add_z r vPAB _ PAB (8 * Z.of_nat i) EPb (eval_sll3 r vIDX (Z.of_nat i) ltac:(unfold vIDX; cbn [eval]; exact E204) ltac:(lia))) by lia. rewrite u64_lit by lia. reflexivity. }
    assert (EvL : bv_unsigned (eval r vLAST) = sc_map_beg lst) by (unfold vLAST; cbn [eval]; rewrite E205, u64_lit by lia; reflexivity).
    cbn [In] in Hin. repeat (destruct Hin as [<-|Hin]); [| | destruct Hin];
      unfold O_cidx, O_lidx, carved in Hz; rewrite obj_range_mk in Hz by lia; rewrite ?EvCI, ?EvL in Hz; cbn [fst snd eval] in Hz; rewrite ?u64_lit in Hz by lia.
    + left. right. right. right. right. right. left. lia.
    + left. right. right. right. right. right. right. exists lst. split; [exact Hl | lia].
Qed.
Lemma In_DUCh : ltac2:(tb__ "0|0|
S0S37S0R1S52Vl;A1A3S37S0R2S3bVcv;A1A3F_;Fo;").
Proof.
  intros o Ho. unfold du_chk in DUOK. apply andb_prop in DUOK as [D1 _]. pose proof (proj1 (forallb_forall _ _) D1 o Ho) as X.
  apply existsb_exists in X as (o' & Ho' & E). apply sobj_eqb_sound in E. subst o'. exact Ho'.
Qed.
Lemma DUo_unk : ltac2:(tb__ "0|0|
S0S37S0R1S3bVcv;A1A3SfS8SaR2A1S4A3F_;Fo;").
Proof.
  intros o Ho. unfold du_chk in DUOK. apply andb_prop in DUOK as [_ D2]. pose proof (proj1 (forallb_forall _ _) D2 o Ho) as Y. cbv beta in Y.
  destruct (ob_dflt o); first [reflexivity | discriminate Y].
Qed.
Lemma DUo_rng : ltac2:(tb__ "0|0|
S0S37S0R1S3bVcv;A1A3S10S0S0SeS37S0R1S57Vl;A1A3SfS1eS4aR3R1A2S20A3A2Lq;A2F_;Fo;").
Proof.
  intros o Ho. pose proof (v_DUorng SC f l cv VOK) as X. apply andb_prop in X as [X _]. pose proof (proj1 (forallb_forall _ _) X o Ho) as Y. cbv beta in Y.
  apply existsb_exists in Y. exact Y.
Qed.

Theorem G_du : ltac2:(tb__ "0|1|
S7S21S1aQ40A1M0A1S5bS54R3A1S51S40VJH;S3eVcv;A1R4R3R2A6S10S7S7SeS51S40VJP;S3dVcv;A1R1R5R4A6S1cSfG0S1R2R1A2S1R7R1A2A3Fv;A2Lr2;A2F_;F_;Fw;Ftp;Fr;").
Proof.
  intros r tp [tr [ms md]] PIN H.
  pose proof (proj2 H) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ. destruct HJ as (rp & HJF & BR).
  pose proof HJF as (Hag & HA & _ & _ & HK & Htp & _ & Htop). pose proof BR as (BW & BL & BOUT & BIN & BRM).
  destruct HPIN as (P151 & P152 & P155 & P12 & P105 & P106).
  assert (RP : forall v, (v < GW)%positive -> rw rp v = rw rho1 v) by (intros v Hv; symmetry; exact (proj1 Hag v Hv)).
  pose proof PIN as (E200 & E201 & E195 & EH & E203 & XF).
  assert (E12 : rw r 12%positive = Z_to_bv 64 p) by (rewrite BW, RP by (unfold GW; lia); exact P12).
  assert (E105 : rw r 105%positive = Z_to_bv 64 (N8 n)) by (rewrite BW, RP by (unfold GW; lia); exact P105).
  pose proof (hbenv_intro Kc HKc A p n i ch HI HU HSZ HN TZ rp r tp tr md HA HK Htp Htop
                ltac:(rewrite RP by (unfold GW; lia); exact P151) ltac:(rewrite RP by (unfold GW; lia); exact P152) ltac:(rewrite RP by (unfold GW; lia); exact P155)
                BR E12 E200 E201 E195) as QS.
  pose proof (nums_of_env r QS) as NM.
  pose proof (proj1 (proj1 H)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  set (R := hv_DUo cv). set (r2 := rho_absorb r R (vms md tp ms)). set (v := view segsA (rm r)). set (v2 := view segsA (rm r2)).
  assert (IRZ : forall x, in_ranges r R x -> DUZh A i ch (bv_unsigned x) \/ (l = false /\ CLZh (bv_unsigned x))).
  { intros x (o & Ho & Hz). destruct (DUo_rng o Ho) as (q & Hq & E). rewrite (SegQ3M_glue.same_rng_range r o q E) in Hz.
    exact (DUp_ranges r q NM PIN E12 E105 Hq _ Hz). }
  assert (PRS : forall z, v z <> None -> v2 z <> None).
  { intros z Hd. destruct (IRdec r R z) as [[Hz Hin]|NI]; [|unfold v2, r2; rewrite (proj2 (absorb_io r R (vms md tp ms)) z NI); exact Hd].
    destruct Hin as (o & Ho & Hr). rewrite u64_lit in Hr by lia.
    destruct (SpineMallocS9.absorb_obj r _ tr (vms md tp ms) (vmd md) (ss_objs (ax_S (hv_EUd cv))) R o Hsm (v_EUxobjs SC f l cv VOK) Ho) as (_ & _ & X3 & _). cbn zeta in X3.
    unfold obj_range in Hr. cbn [fst snd] in Hr.
    destruct (X3 (or_introl (DUo_unk o Ho)) (z - bv_unsigned (eval r (ob_base o))) ltac:(lia)) as [x Hx].
    unfold v2, r2. rewrite view_in by lia.
    replace (Z_to_bv 64 z) with (Z_to_bv 64 (bv_unsigned (eval r (ob_base o)) + (z - bv_unsigned (eval r (ob_base o))))) by (f_equal; lia).
    rewrite Hx. discriminate. }
  assert (CELL : forall o c bz off k val, In o R -> In c (ob_cells o) -> bv_unsigned (eval r (ob_base o)) = bz -> soff r (c_off c) = off ->
            c_width c = Z.of_nat k -> eval r (SymState.c_val c) = Z_to_bv 64 val -> 0 <= bz + off -> bz + off + Z.of_nat k <= 2 ^ 64 -> cell_ok v2 (mkACell (bz + off) k val)).
  { intros o c bz off k val Ho Hc Eb Eo W Ev B1 B2 j Hj. cbn [c_addr c_w RtCells.c_val] in *.
    destruct (SpineMallocS9.absorb_obj r _ tr (vms md tp ms) (vmd md) (ss_objs (ax_S (hv_EUd cv))) R o Hsm (v_EUxobjs SC f l cv VOK) Ho) as (_ & X2 & _). cbn zeta in X2.
    destruct (X2 c Hc) as (_ & _ & Xc). specialize (Xc j ltac:(rewrite W, Nat2Z.id; exact Hj)). rewrite Eb, Eo, W, Nat2Z.id, Ev in Xc.
    unfold v2, r2. rewrite view_in by lia. exact Xc. }
  unfold NUMSh in NM. destruct NM as (P0 & P1 & N1 & N8' & LTi & L0 & L1 & L2 & H0 & H1 & H2 & PP & PBAND).
  pose proof (topG_range G) as TG. unfold IMG_HI, kPtrArrayReserve in *.
  assert (EPb : eval r vPAB = Z_to_bv 64 PAB) by (unfold vPAB; cbn [eval]; exact E200).
  assert (ENc : eval r vNCH = Z_to_bv 64 NC) by (unfold vNCH; cbn [eval]; exact E201).
  assert (EHv : eval r vH = Z_to_bv 64 h) by (unfold vH; cbn [eval]; exact EH).
  assert (EvCL : bv_unsigned (eval r (add (SAlu ALU_SLL vNCH (SLit 3)) vPAB)) = 8 * NC + PAB).
  { rewrite (eval_add_z r _ vPAB _ _ (eval_sll3 r vNCH _ ENc ltac:(lia)) EPb) by lia. rewrite u64_lit by lia. reflexivity. }

  assert (CN : cell_ok v2 (mkACell (SEC_INST + 56) 8 (NC - 1))).
  { apply (CELL _ (mkCell (SLit 974352) 8 (add vNCH (SLit (-1)))) 0 974352 8%nat _ (In_DUCh _ ltac:(unfold DUCh; apply in_or_app; left; left; reflexivity)));
      [left; reflexivity | reflexivity | apply soff_lit_small; lia | reflexivity | | lia | lia].
    cbn [SymState.c_val]. replace (NC - 1) with (NC + -1) by lia. apply ev_add_lit; [exact ENc | lia | lia | lia]. }
  assert (CM : cell_ok v2 (mkACell 0xee040 4 0)).
  { assert (HIN : In (mkObj (SLit 0) (SLit 974912) (SLit 974916) [mkCell (SLit 974912) 1 (SLit 0); mkCell (SLit 974913) 3 (SLit 0)] DUnknown) R)
      by (apply In_DUCh; unfold DUCh; apply in_or_app; left; right; left; reflexivity).
    pose proof (CELL _ (mkCell (SLit 974912) 1 (SLit 0)) 0 974912 1%nat 0 HIN ltac:(left; reflexivity) eq_refl ltac:(apply soff_lit_small; lia) eq_refl eq_refl ltac:(lia) ltac:(lia)) as M0.
    pose proof (CELL _ (mkCell (SLit 974913) 3 (SLit 0)) 0 974913 3%nat 0 HIN ltac:(right; left; reflexivity) eq_refl ltac:(apply soff_lit_small; lia) eq_refl eq_refl ltac:(lia) ltac:(lia)) as M1.
    unfold cell_ok in M0, M1. cbn [c_addr c_w RtCells.c_val] in M0, M1.
    intros k Hk. cbn [c_addr c_w RtCells.c_val] in *. destruct k as [|[|[|[|k]]]]; [| | | | lia].
    - replace (974912 + Z.of_nat 0) with (0 + 974912 + Z.of_nat 0) by lia. rewrite (M0 0%nat ltac:(lia)). reflexivity.
    - replace (974912 + Z.of_nat 1) with (0 + 974913 + Z.of_nat 0) by lia. rewrite (M1 0%nat ltac:(lia)). reflexivity.
    - replace (974912 + Z.of_nat 2) with (0 + 974913 + Z.of_nat 1) by lia. rewrite (M1 1%nat ltac:(lia)). reflexivity.
    - replace (974912 + Z.of_nat 3) with (0 + 974913 + Z.of_nat 2) by lia. rewrite (M1 2%nat ltac:(lia)). reflexivity. }
  pose proof (hb_hsr _ _ _ _ _ QS) as (SC1 & _). fold v in SC1.
  assert (CF : l = false -> cell_ok v2 (mkACell (PAB + 8 * Z.of_nat i) 8 (sc_map_beg lst)) /\ cell_ok v2 (mkACell (sc_map_beg lst + 24) 8 (Z.of_nat i))
                            /\ (forall z, CLZh z -> v2 z = v z)).
  { intros El. destruct (XF El) as (E204 & E205). pose proof (HLF El) as XLT.
    assert (EvCI : bv_unsigned (eval r (add vPAB (SAlu ALU_SLL vIDX (SLit 3)))) = PAB + 8 * Z.of_nat i).
    { rewrite (eval_add_z r vPAB _ _ (8 * Z.of_nat i) EPb (eval_sll3 r vIDX (Z.of_nat i) ltac:(unfold vIDX; cbn [eval]; exact E204) ltac:(lia))) by lia. rewrite u64_lit by lia. reflexivity. }
    assert (EvL : bv_unsigned (eval r vLAST) = sc_map_beg lst) by (unfold vLAST; cbn [eval]; rewrite E205, u64_lit by lia; reflexivity).
    assert (IN1 : In (mkObj (add vPAB (SAlu ALU_SLL vIDX (SLit 3))) (SLit 0) (SLit 8) [mkCell (SLit 0) 8 vLAST] DUnknown) R)
      by (apply In_DUCh; unfold DUCh; rewrite El; apply in_or_app; right; left; reflexivity).
    assert (IN2 : In (mkObj (add (SAlu ALU_SLL vNCH (SLit 3)) vPAB) (SLit (-8)) (SLit 0) [mkCell (SLit (-8)) 8 vLAST] DUnknown) R)
      by (apply In_DUCh; unfold DUCh; rewrite El; apply in_or_app; right; right; left; reflexivity).
    assert (IN3 : In (mkObj vLAST (SLit 24) (SLit 32) [mkCell (SLit 24) 8 vIDX] DUnknown) R)
      by (apply In_DUCh; unfold DUCh; rewrite El; apply in_or_app; right; right; right; left; reflexivity).
    split; [|split].
    - replace (PAB + 8 * Z.of_nat i) with (PAB + 8 * Z.of_nat i + 0) by lia.
      apply (CELL _ (mkCell (SLit 0) 8 vLAST) _ 0 8%nat _ IN1); [left; reflexivity | exact EvCI | apply soff_lit_small; lia | reflexivity | unfold vLAST; cbn [SymState.c_val eval]; exact E205 | lia | lia].
    - apply (CELL _ (mkCell (SLit 24) 8 vIDX) _ 24 8%nat _ IN3); [left; reflexivity | exact EvL | apply soff_lit_small; lia | reflexivity | unfold vIDX; cbn [SymState.c_val eval]; exact E204 | lia | lia].
    - pose proof (CELL _ (mkCell (SLit (-8)) 8 vLAST) _ (-8) 8%nat _ IN2 ltac:(left; reflexivity) EvCL ltac:(apply soff_lit_small; lia) eq_refl ltac:(unfold vLAST; cbn [SymState.c_val eval]; exact E205) ltac:(lia) ltac:(lia)) as CL2.
      destruct (SC1 _ lst Hl) as (_ & _ & _ & _ & CLv & _).
      intros z Hz. unfold CLZh in Hz. apply (cell_ok_same v v2 _ CLv); [|cbn [c_addr c_w]; fold G PAB; unfold NC in *; rewrite Nat2Z.inj_sub by lia; cbn [Z.of_nat]; lia].
      fold G PAB. replace (PAB + 8 * Z.of_nat (length (aa_sec A) - 1)) with (8 * NC + PAB + -8) by (unfold NC; rewrite Nat2Z.inj_sub by (unfold NC in *; lia); cbn [Z.of_nat]; lia). exact CL2. }
  assert (CT : l = true -> forall z, PAB + 8 * Z.of_nat i <= z < PAB + 8 * Z.of_nat i + 8 -> v2 z = v z).
  { intros El. pose proof (HLT El) as EI.
    assert (IN1 : In (mkObj (add (SAlu ALU_SLL vNCH (SLit 3)) vPAB) (SLit (-8)) (SLit 0) [mkCell (SLit 18446744073709551608) 8 vH] DUnknown) R)
      by (apply In_DUCh; unfold DUCh; rewrite El; apply in_or_app; right; left; reflexivity).
    pose proof (CELL _ (mkCell (SLit 18446744073709551608) 8 vH) _ (-8) 8%nat h IN1 ltac:(left; reflexivity) EvCL ltac:(reflexivity) eq_refl ltac:(cbn [SymState.c_val]; exact EHv) ltac:(lia) ltac:(lia)) as CL2.
    destruct (SC1 i ch HI) as (_ & _ & _ & _ & CPv & _). fold G PAB h in CPv.
    intros z Hz. apply (cell_ok_same v v2 _ CPv); [|cbn [c_addr c_w]; lia].
    replace (PAB + 8 * Z.of_nat i) with (8 * NC + PAB + -8) by (unfold NC in *; lia). exact CL2. }
  assert (EQF : forall z, ~ DUZh A i ch z -> v2 z = v z).
  { intros z ND. destruct (IRdec r R z) as [[Hz Hin]|NI]; [|exact (proj2 (absorb_io r R (vms md tp ms)) z NI)].
    pose proof (IRZ _ Hin) as X0. rewrite u64_lit in X0 by lia. destruct X0 as [X0|[El X0]]; [exfalso; exact (ND X0)|]. exact (proj2 (proj2 (CF El)) z X0). }
  pose proof (qs_chunk A (p, n) i ch r QS) as (_ & _ & _ & _ & _ & CB & _). cbn [fst snd] in CB. fold h msz in CB.
  assert (SHB : forall z, chunk_sh_zone ch z -> SHADOW_BAND_LO <= z < SHADOW_BAND_HI).
  { intros z Hz. exact (shz_bandz ch ltac:(fold h; lia) ltac:(fold msz; lia) ltac:(fold h msz; lia) z Hz). }
  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  assert (HT : SPA segsA TJ (hv_EUx cv) r tp (tr, mkCfg ms md)) by (split; [exact (proj1 H) | exact I]).
  pose proof (SPA_unobj segsA TJ r (hv_EUx cv) (ss_objs (ax_S (hv_EUd cv))) R tp tr ms md (v_EUxobjs SC f l cv VOK) HT (fun x => x)) as HU2. cbn zeta in HU2. fold r2 in HU2.
  rewrite (v_EUdset SC f l cv VOK) in HU2.
  exists r2. split; [|intros v0; reflexivity].
  split; [exact (proj1 HU2)|]. cbn [w_tr w_cfg cfg_model fst snd]. unfold JP, JPh. exists rp. split; [exact HJF|].
  split; [|split; [exact CN | split; [exact CM | split; [intros El; destruct (CF El) as (X1 & X2 & _); split; [exact X1 | exact X2]|]]]].
  - split; [intros v0; exact (BW v0)|]. split; [intros l0; exact (BL l0)|]. split; [|split].
    + intros z ND. change (v2 z = view segsA (rm rp) z). rewrite (EQF z ND). apply BOUT. intros HS. apply ND. right. left. exact HS.
    + intros z HD Hp. change (v2 z <> None). apply PRS. unfold v.
      destruct (Z_le_dec (Sh h) z) as [Q1|Q1]; [destruct (Z_lt_dec z (Sh (h + msz))) as [Q2|Q2]|].
      * apply BIN; [unfold chunk_sh_zone; fold h msz; lia | exact Hp].
      * rewrite BOUT; [exact Hp | unfold chunk_sh_zone; fold h msz; lia].
      * rewrite BOUT; [exact Hp | unfold chunk_sh_zone; fold h msz; lia].
    + intros a0 NT. rewrite <- (BRM a0 NT). apply (proj1 (absorb_io r R (vms md tp ms))). intros Hin. apply NT.
      destruct (IRZ _ Hin) as [X0|[_ X0]]; [exact (HZT _ X0) | apply HZTt; unfold CLZh in X0; lia].
  - intros El z Hz. change (v2 z = view segsA (rm rp) z). rewrite (CT El z Hz). apply BOUT. intros HS. pose proof (SHB z HS) as HB0. clear -Hz LTi N8' PBAND HB0. unfold PAB, G in *. lia.
Qed.
End Du.
End F0A_hbN_du.

(* [comment removed for export] *)
Module F0A_hbN_exit.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "ex"; "iff"; "False"; "@Corelib.Init.Datatypes"; "prod"; "cons"; "list"; "pair"; "bool"; "fst"; "nat"; "nil"; "snd"; "app"; "false"; "option"; "true"; "None"; "andb"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "pow"; "modulo"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "rw"; "sv"; "rm"; "valuation"; "odefault"; "ob_dflt"; "rl"; "ss_objs"; "DUnknown"; "SVar"; "eval"; "obj_range"; "smatch"; "tfact"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cw.F0A_hbN_exit"; "ROSh"; "TZh"; "Prosh"; "STSH"; "XKh"; "XRh"; "qsz_spec"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "client_addrA"; "client_shadowA"; "UStopLe"; "AE_A"; "JL_free"; "L_free"; "Wcan"; "mem_keptA"; "top_high"; "tp_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue"; "spec_range"; "coverb"; "spec_covered"; "spec_small"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_unmap"; "DUZh"; "JH2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "ag_ctx"; "ag_spacebeg"; "ag_pab"; "ag_thread"; "aa_live"; "ageom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "sobj_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "SEC_INST"; "IA_BEG"; "IA_END"; "fs_footb"; "fs_inv"; "geom_ok"; "live_sep"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states"; "XM_hb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "kSpaceSize"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "in_rangesZ"; "restrictv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "QRD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4"; "chunk_zone"; "chunk_sh_zone"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "vmd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "cells_in_view"; "rd_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.F0A_exit"; "sv_varsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs"; "nocellsF"; "NRTX"; "REST_of"; "XK_of"; "XR_of"; "nkeep"; "sX_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_entry"; "N_hb";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cw.F0A_hbN_exit.ExitH"; "EXPIN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "O_stQ"; "O_stT1"; "O_stT2"; "cQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.InvQ11"; "freeBigA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundW SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv ReprGlue Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 RebuildM InvLaws SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.F0A_exit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2 SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_blind.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_hbN_cert.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQ7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.InvQ10b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.InvQ11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.F0A_rebuildW OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.F0A_rzone OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_blind OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_entry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_unmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition qsz_spec : carve_spec := ltac2:(tb__ "0|4|
ScS9S9S23S0A2M0S0A2SbS9S9S0SfA2M1S23A2M2A1ScG0S0ScS23S0S8cZ18M3A4Z20A4SaG2ScG1S23ScS0SfG3U8A4S2bP7bA1A4S10G2A1A3A4").

Definition ROSh : list carve_spec := ltac2:(tb__ "0|0|
S12S19S7dS12S19S72S19U3S85A3SaS19S3bS10S19A1A3A3A3").

Definition STSH : list sobj := ltac2:(tb__ "0|0|
S73S21S21S7cSaS21S8aSaS21S89SaS21S8bS10S21A1A3A3A3A4").
Definition rclshb (R : list sobj) : bool := ltac2:(tb__ "0|0|
S3dS21S21S18S3eS21S58R1A1S73S19S21S1aS35A4A3S3eS21S58S7cR1A1A1S38A3A2Lo;VR;A3").
Definition rcivhb (R : list sobj) : bool := ltac2:(tb__ "0|0|
S3dS19S19S3eS21S58S1aR1A1A1VR;A3Lk;S35A3").
Definition runkb (R : list sobj) : bool := ltac2:(tb__ "0|1|
S3dS21S21S26SdLx;S27R1A1S15S13S13S1S13Ll;M0G0S0S23SbS9S0S0A2A1SbS2fA1S13Ltmpl;Lflds;Lcnt;Lesz;X26x6Lo;VR;A3").

Definition XKh (nW : nat) (XF : axst) : axst := ltac2:(tb__ "0|0|
S7fVnW;S67VXF;A1A2").
Definition KEPTh (nW : nat) (XF : axst) : list sobj := ltac2:(tb__ "0|0|
S72S21S81VnW;A1S29S57S67VXF;A1A1A1A3").
Definition RESTh (nW : nat) (XF : axst) : list sobj := ltac2:(tb__ "0|0|
S7eVnW;S67VXF;A1A2").
Definition XRh (nW : nat) (XF : axst) : axst := ltac2:(tb__ "0|0|
S80S39VnW;VXF;A2A1").
Definition sXh (nW : nat) (XF : axst) : wsub := ltac2:(tb__ "0|0|
S82S3aVnW;VXF;A2S45VnW;A1S41A3").
Record hbexit_ok (nW : nat) (XF : axst) : Prop := mkHBX {
  x_AXE : apply_axforms XF (XEX_hb XF) = Some (XM_hb XF);
  x_WXR : swf (ax_S (XRh nW XF)) = true;
  x_DXR : state_diff (ax_S (XKh nW XF)) (ax_S (XRh nW XF)) = Some ([(SLit TP_A, SVar 24)], []);
  x_NXR : ss_next (ax_S (XRh nW XF)) = ss_next (ax_S (XKh nW XF));
  x_EQR : ax_setS (XKh nW XF) (ax_S (XRh nW XF)) = XRh nW XF;
  x_ENT : entailsA (XRh nW XF) (L_free AE_A (Wcan nW) UStopLe) (sXh nW XF) = true;
  x_SID : wsub_id_below (sXh nW XF) NF = true;
  x_RCLS : rclshb (RESTh nW XF) = true;
  x_RCIV : rcivhb (RESTh nW XF) = true;
  x_RUNK : runkb (RESTh nW XF) = true
}.

Lemma ROSh_small : Forall spec_small ROSh.
Proof.
  unfold ROSh. apply Forall_app. split; [exact NRTX_small|].
  unfold N_hb, qsz_spec, spec_small, SEC_INST. cbn [firstn app].
  repeat apply Forall_cons; try apply Forall_nil; (split; [lia|]); (split; [lia|]); (split; [lia|]); unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia.
Qed.
Lemma ROSh_coverb : ltac2:(tb__ "0|0|
S3SdS3dS19S4aS35A3S15A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition Prosh (i : positive) : bool := ltac2:(tb__ "0|0|
S3eS1S8fVi;A1SaS1PcSaS1P88SaS1P97SaS1P98SaS1P99SaS1P9aSaS1P9bSaS1P7bSaS1Pc3SaS1Pc8S10S1A1A3A3A3A3A3A3A3A3A3A3A3").
Lemma ROSh_varsb : ltac2:(tb__ "0|5|
S3SdS3dS19S19S9S9S9S23S0A2M0S0A2M1SbS9S9S0SfA2M2S23A2M3A1M4A2SdLk;R1G1G4G1SdLp;R2G0S0G0SdLp0;R2S23S0S17S7bS37R2A2S3dG3G3G3SdLc;R1G2S23G2SdLp;R2S0SfS7bS37R3A2Ln;Lz;X9x1Le;Lp;X9x1Lc;R5A3A2Lz0;Lb;X9x1Lz;Lp0;X9x1Lcs;Lp;X9x1Lk;S35A3S15A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma ROSh_zone : ltac2:(tb__ "0|8|
S54S25S19S0S61R4A1S3S30Q40M0A1M1S22R4P97A2S31G0S52R5A1A2A3S3G1S22R5P98A2S31G0S4fR6A1A2A3S2S1bZ0M2S32G0S22R6PcA2A2M3A2S1cG3S1eZ2Z2fA2A2A2S3cS19R6S35A3S2S1bSeS0S0S49R8R7A2M4A3R6A2S1cR6S11S0S0G4A3A2A2S5S2S2S1bG2R7A2S1cR7S68A2A2S4S2S1bS1dS5cZ38A2R7A2S1cR7Zee070A2A2A1A2S5S2S1bS52RaA1M5R7A2S1cR7S1dG5Z1000M6A2A2A2S2S1bS4fRaA1M7R7A2S1cR7S1dG7G6A2A2A2A2A2F_;F_;F_;F_;F_;F_;Fa;Fk;Frho;FG;").
Proof.
  intros G rho k a HG E151 E152 B12 Hk Ha.
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & _). pose proof (topG_range G) as TG.
  assert (LITOK : forallb (fun k : carve_spec => let '(b, lo, hi, _) := k in
             negb (sv_eqb b (SLit 0)) || ((0 <=? lo) && (hi <=? IMG_HI) && ((hi <=? SEC_INST + 56) || (0xee070 <=? lo)))) ROSh = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof (proj1 (forallb_forall _ _) LITOK k Hk) as LK.
  destruct k as [[[b lo] hi] cs]. destruct (sv_eqb b (SLit 0)) eqn:EB.
  - apply sv_eqb_sound in EB. subst b. cbn [negb orb] in LK. apply andb_prop in LK as [LK L3]. apply andb_prop in LK as [L1 L2].
    apply Z.leb_le in L1. apply Z.leb_le in L2. apply orb_prop in L3.
    cbn [spec_range fst snd eval] in Ha. unfold IMG_HI in *. rewrite u64_lit in Ha by lia. left.
    destruct L3 as [L3|L3]; apply Z.leb_le in L3; lia.
  - clear LK LITOK. unfold ROSh, NRTX, N_rest, N_fn, N_hb, qsz_spec in Hk. cbn [tl app In firstn] in Hk. unfold cQ, vT, vCTX, vTOP, vBOT, vSB, vMINq, iam_base, vRISh, vPAB in Hk.
    repeat (destruct Hk as [E|Hk]; [injection E as <- <- <- <-; cbn in EB; try discriminate; cbn [spec_range fst snd eval] in Ha; rewrite ?E151, ?E152, ?add_val, ?u64_lit in Ha by lia |]).
    all: try (right; lia).
    all: try (right; left; rewrite Z.mod_small in Ha by lia; lia).
    all: try (destruct Hk).

    left. rewrite sll_val, srl_val in Ha. change (32 mod 64) with 32 in Ha. change (3 mod 64) with 3 in Ha.
      rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 in Ha by lia.
      pose proof (Z.div_lt_upper_bound (bv_unsigned (rw rho 12%positive)) (2 ^ 32) (2 ^ 15) ltac:(lia) ltac:(lia)).
      pose proof (Z.div_pos (bv_unsigned (rw rho 12%positive)) (2 ^ 32) ltac:(lia) ltac:(lia)).
      rewrite Z.mod_small in Ha by lia. unfold IMG_HI, SEC_INST. lia.
Qed.

Definition TZh (A : AA) (ch : sec_chunk) (z : Z) : Prop := ltac2:(tb__ "0|0|
S5S6fVA;Vz;A2S5S70Vch;Vz;A2S71Vch;Vz;A2A2A2").

Section ExitH.
Local Notation segs := segsA (only parsing).
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S0S6dVCST;R1A2S5S6dS88R2A2S2S1bS5dR2A2S1cR2S5eA2A2A2S8F_;F_;Fa;").
Variable nW : nat.
Let W : list ulink := Wcan nW.
Variable XF : axst.
Hypothesis XOK : hbexit_ok nW XF.
Variables (A : AA) (Kc : KcA) (rho : valuation) (tp : list word) (p n t : Z) (jv : junkF) (keep : Z -> Prop).
Variables (A' : AA) (rho1' : valuation) (l1 l2 : list (Z * Z)) (i : nat) (ch : sec_chunk).
Let rho1 : valuation := ltac2:(tb__ "0|0|
S87VA;Vrho;Vp;Vn;Vt;Vjv;A6").
Let A2 : AA := ltac2:(tb__ "0|0|
S8dVA';Vl1;Vl2;Vi;A4").
Let G : ageom := aa_geom A'.
Let T : Z := ag_thread G.
Let h : Z := sc_map_beg ch.
Let msz : Z := sc_map_size ch.
Let XM : axst := XM_hb XF.
Let XK : axst := XKh nW XF.
Let XR : axst := XRh nW XF.
Let KEPT : list sobj := KEPTh nW XF.
Let REST : list sobj := RESTh nW XF.
Let sX : wsub := sXh nW XF.
Hypothesis HKc : Kc_ok Kc.
Hypothesis Hp12 : ltac2:(tb__ "0|0|
S3S0S32Q40S22Vrho;PcA2A2Vp;A3").
Hypothesis Hn13 : ltac2:(tb__ "0|0|
S3S0S32Q40S22Vrho;PdA2A2Vn;A3").
Hypothesis HR : rigF rho rho1.
Hypothesis HDO : depot_onlyKf A A'.
Hypothesis HLK : ltac2:(tb__ "0|0|
S8eVkeep;Vrho1;Vrho1';A3").
Hypothesis HKEEP : ltac2:(tb__ "0|0|
S0S5S3fVCST;VA;R1A3S40VCST;VXGL;VA;R1A4A2Vkeep;R2A1F_;Fa;").
Hypothesis HLV : ltac2:(tb__ "0|1|
S3SbS9S0S0A2M0A1S53VA';A1S12G0Vl1;SaG0ScS0S0Vp;Vn;A4Vl2;A3A3A3").

Hypothesis HPIN : ltac2:(tb__ "0|2|
S2S3S30Q40M0A1M1S22Vrho1';P97A2S31G0VT;A2A3S2S3G1S22Vrho1';P98A2S31G0S4fVG;A1A2A3S2S3G1S22Vrho1';P9bA2S31G0S50VG;A1A2A3S2S3G1S22Vrho1';PcA2S31G0Vp;A2A3S2S1bZ0Vp;A2S1cVp;S1eZ2Z2fA2A2A2A2A2A2A2").

Hypothesis HZ_T : ltac2:(tb__ "0|0|
S0S2S1bVT;R1A2S1cR1S1dVT;Z1000A2A2A2S4S4dVA';Vi;Vch;R2A4A1F_;Fz;").
Hypothesis HZ_C : ltac2:(tb__ "0|1|
S0S2S1bS4fVG;A1M0R1A2S1cR1S1dG0Z1000A2A2A2S4S4dVA';Vi;Vch;R2A4A1F_;Fz;").
Hypothesis HZ_L : ltac2:(tb__ "0|0|
S0S2S1bZ0R1A2S1cR1S68A2A2S4S2S1bS1dS5cZ38A2R2A2S1cR2Zee070A2A2A1S4S4dVA';Vi;Vch;R3A4A1F_;F_;Fz;").
Hypothesis CHB : ltac2:(tb__ "0|3|
S2S3S0S1fVh;Z8M0A2Z0M1A3S2S3S0S1fVmsz;G0A2G1A3S2S1bS68Vh;A2S2S1bG1Vmsz;A2S2S1cS1dVh;Vmsz;A2M2S1eZ2Z2fA2A2S5S1bG2S6bA2S1bS6aVh;A2A2A2A2A2A2A2").

Hypothesis HNQ : ltac2:(tb__ "0|0|
S0S3fVCST;VA';R1A3S4S6fVA';R2A2A1F_;Fa;").
Hypothesis HNQS : ltac2:(tb__ "0|0|
S0S40VCST;VXGL;VA';R1A4S4S6fVA';R2A2A1F_;Fa;").
Hypothesis HNOC : ltac2:(tb__ "0|0|
S0S3fVCST;VA2;R1A3S4S70Vch;R2A2A1F_;Fy;").

Definition EXPIN (r : valuation) : Prop := ltac2:(tb__ "0|2|
S2S1S90R1S34A2S3S30Q40M0A1M1S22Vr;R2A2S22Vrho1';R2A2A3F_;Fv;S2S1S3SbS30Q8A1A1S28Vr;R1A2S28Vrho1';R1A2A3Fl;S2S3G1S22Vr;Pc3A2S31G0S1dS50VG;A1S69A2A2A3S3G1S22Vr;Pc8A2S31G0S51VG;A1A2A3A2A2A2").
Hypothesis LFRO : ltac2:(tb__ "0|4|
S25S86R1A1S19S3cS19R1S35A3S79R4S7aS33S24Vrho1';A1A2S20SeS0S0S49R4R2A2A3S9S9S9S23S0A2M0S0A2M1SbS9S9S0SfA2S23A2A1M2A2M3S0Lk;R2G1G2G1S0Lp0;R2G0S0G0S0Lp1;R2S23S0R1Llo;Ls;X9x1Lz;Lp1;X9x1Ll;Lp0;X9x1A2G3G2Lk;R2G1G2G1G2Lp0;R2G0S0G0G2Lp1;R2S23S0R5Lz0;Ls;X9x1Lz;Lp1;X9x1Lcs;Lp0;X9x1A4F_;Fk;F_;Fr;").

Section FINH.
Variables (r : valuation) (tpX : list word) (tr : list event) (ms : machine_state) (md : Model).
Let w : world := ltac2:(tb__ "0|0|
ScSbS63A1S74Vtr;S75Vms;Vmd;A2A4").
Hypothesis HEP : EXPIN r.
Hypothesis H : ltac2:(tb__ "0|0|
S55S33S4eVKc;VA';Vrho1';Vl1;Vl2;Vi;Vch;S36VA';Vch;A2A8VXF;Vr;VtpX;Vw;A6").
Let KJ : jpredA := ltac2:(tb__ "0|0|
S25SbS30Q40A1A1SbS63A1S64VKc;R2R1A2Lm0;Lt0;L_;L_;").
Let rho3 : valuation := ltac2:(tb__ "0|0|
S66Vr;VREST;S77Vmd;VtpX;Vms;A3A3").
Let v3 : bview := ltac2:(tb__ "0|0|
S6cS33S24Vrho3;A1A2").
Let vr : bview := ltac2:(tb__ "0|0|
S6cS33S24Vr;A1A2").

Lemma J2 : ltac2:(tb__ "0|5|
S2S5bS33VA2;Vr;VtpX;Vmd;A5S2VKc;Vtr;Vmd;A2S2S48VA2;Vr;A2S2S47VA2;Vr;A2S2S30Q40M0A1S4S36VA';Vch;S32G0R1A2A3A1S3S14S30Q8A1M1A1M2S24Vr;R2A2S24Vrho1';R2A2A3F_;Fa;S2S0S4S4dVA';Vi;Vch;R1A4A1S3G2Vvr;R2A1S6cS33S24Vrho1';A1R2A3M3A3F_;Fz;S0S4S70Vch;R1A2A1S4S3G2G3S16G1A1M4A3A1S4S3G2Vvr;R3A1G4A3A1F_;F_;Fz;A2A2A2A2A2A2").
Proof. destruct H as [_ (X1 & X2 & X3 & X4 & _ & _ & X7 & X8 & X9)]. exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X7 (conj X8 X9)))))). Qed.
Lemma E151 : ltac2:(tb__ "0|1|
S3S30Q40M0A1S22Vr;P97A2S31G0VT;A2A3"). Proof. rewrite (proj1 HEP) by (unfold GW; lia). exact (proj1 HPIN). Qed.
Lemma E152 : ltac2:(tb__ "0|1|
S3S30Q40M0A1S22Vr;P98A2S31G0S4fVG;A1A2A3"). Proof. rewrite (proj1 HEP) by (unfold GW; lia). exact (proj1 (proj2 HPIN)). Qed.
Lemma B12 : ltac2:(tb__ "0|1|
S2S1bZ0S32Q40S22Vr;PcA2A2M0A2S1cG0S1eZ2Z2fA2A2A2").
Proof. rewrite (proj1 HEP) by (unfold GW; lia). destruct HPIN as (_ & _ & _ & E & B). rewrite E, u64_lit by lia. exact B. Qed.
Lemma E155 : ltac2:(tb__ "0|1|
S3S30Q40M0A1S22Vr;P9bA2S31G0S50VG;A1A2A3"). Proof. rewrite (proj1 HEP) by (unfold GW; lia). exact (proj1 (proj2 (proj2 HPIN))). Qed.
Lemma HG2 : geom_ok G. Proof. pose proof (proj1 J2) as (HG & _). exact HG. Qed.

Lemma Ha : ltac2:(tb__ "0|0|
S55S33VKJ;VXM;Vr;VtpX;Vw;A6").
Proof.
  destruct (SPA_axforms segs KJ (XEX_hb XF) r XF XM tpX w (x_AXE nW XF XOK) ltac:(split; [exact (proj1 H) | exact (proj1 (proj2 J2))])) as [X Y]. split; assumption.
Qed.
Lemma Hsm1 : ltac2:(tb__ "0|0|
S2eS33Vr;S57VXM;A1ScSbS63A1S74Vtr;S75S77Vmd;VtpX;Vms;A3S78Vmd;A1A2A4A4").
Proof. pose proof (proj1 (proj1 Ha)) as X. unfold virt in X. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in X. exact X. Qed.
Lemma OBJS : ltac2:(tb__ "0|0|
S3SbS21A1S29S57VXM;A1A1S12S21VKEPT;VREST;A3A3").
Proof. unfold KEPT, REST, KEPTh, RESTh, REST_of. symmetry. apply firstn_skipn. Qed.
Lemma Hb : ltac2:(tb__ "0|0|
S55S33VKJ;VXK;Vrho3;VtpX;Vw;A6").
Proof. exact (SPA_unobj segs KJ r XM KEPT REST tpX tr ms md OBJS Ha (fun k => k)). Qed.

Lemma RCIV' : ltac2:(tb__ "0|0|
S19S3cS19R1S35A3S3cS21S1aR2A1VREST;A3F_;Fk;").
Proof.
  intros k Hk. pose proof (proj1 (forallb_forall _ _) (x_RCIV nW XF XOK) k Hk) as X. apply existsb_exists in X as (o & Ho & E).
  apply sobj_eqb_sound in E. subst o. exact Ho.
Qed.
Lemma RUNK' : ltac2:(tb__ "0|0|
S21S3cS21R1VREST;A3S3S26S27R2A1S2aA3F_;Fo;").
Proof. intros o Ho. pose proof (proj1 (forallb_forall _ _) (x_RUNK nW XF XOK) o Ho) as Y. cbv beta in Y. destruct (ob_dflt o); first [reflexivity | discriminate Y]. Qed.
Lemma EvT : ltac2:(tb__ "0|0|
S3S0S32Q40S2cVr;S84A2A2VT;A3").
Proof. pose proof (geom_numsS _ HG2) as (_ & _ & _ & G4 & G5 & _). pose proof (topG_range G). unfold vT. cbn [eval]. rewrite E151. apply u64_lit. fold T in G4, G5. lia. Qed.
Lemma RCLS' : ltac2:(tb__ "0|2|
S21S0S3cS21R2VREST;A3S2S1bSeS0S0S2dVr;R3A2M0A3R2A2S1cR2S11S0S0G0A3A2A2S5S6S19S19S2S3cS19R1S35A3S2S1bSeS0S0S49Vr;R1A2M1A3R4A2S1cR4S11S0S0G1A3A2A2A2Lk;A2S2S1bS1dVT;Zad0A2R3A2S1cR3S1dVT;Zc60A2A2A2A2F_;F_;Fa;Fo;").
Proof.
  intros o a Ho Ha0. pose proof (proj1 (forallb_forall _ _) (x_RCLS nW XF XOK) o Ho) as X. cbv beta in X. apply orb_prop in X as [X|X].
  - apply existsb_exists in X as (o' & Ho' & E). apply sobj_eqb_sound in E. subst o'. apply in_map_iff in Ho' as (k & <- & Hk). left. exists k. split; [exact Hk|].
    rewrite (carve_range XK XK eq_refl A r k (proj1 (Forall_forall _ _) ROSh_small k Hk)) in Ha0. exact Ha0.
  - right. apply existsb_exists in X as (s & Hs & E). apply sobj_eqb_sound in E. rewrite <- (nocells_range r o), E in Ha0.
    pose proof (geom_numsS _ HG2) as (_ & _ & _ & G4 & G5 & _). pose proof (topG_range G) as TG. fold T in G4, G5. pose proof EvT as ET.
    unfold STSH in Hs. cbn [map In] in Hs. destruct Hs as [<-|[<-|[<-|[]]]]; unfold nocellsF, O_stT1, O_stQ, O_stT2, carved, cA in Ha0; cbn [ob_base ob_lo ob_hi ob_dflt] in Ha0;
      rewrite obj_range_mk in Ha0 by lia; cbn [fst snd] in Ha0.
    + rewrite ET in Ha0. lia.
    + cbn [eval] in Ha0. rewrite add_val, u64_lit in Ha0 by lia. change (rw r 151%positive) with (eval r vT) in Ha0. rewrite ET in Ha0. rewrite Z.mod_small in Ha0 by lia. lia.
    + rewrite ET in Ha0. lia.
Qed.

Lemma RO_off : ltac2:(tb__ "0|1|
S19S0S3cS19R2S35A3S2S1bSeS0S0S49Vr;R3A2M0A3R2A2S1cR2S11S0S0G0A3A2A2S2S4S4dVA';Vi;Vch;R3A4A1S2S1bZ0R3A2S1cR3S1eZ2Z2fA2A2A2A2F_;F_;Fa;Fk;").
Proof.
  intros k a Hk Ha0. pose proof (geom_numsS _ HG2) as (_ & _ & _ & G4 & G5 & G6 & G7 & _). pose proof (topG_range G) as TG. fold T in G4, G5.
  destruct (ROSh_zone G r k a HG2 E151 E152 B12 Hk Ha0) as [[Z1 Z2]|[Z1|Z1]].
  - split; [exact (HZ_L a Z1 Z2) | unfold IMG_HI in Z1; lia].
  - split; [exact (HZ_T a Z1) | fold T in Z1; lia].
  - split; [exact (HZ_C a Z1) | lia].
Qed.
Lemma NKr : ltac2:(tb__ "0|4|
S19S3cS19R1S35A3S2S3cS21S1aR2A1VREST;A3S2S4cR2A1S2S4bR2A1S79Vr;S7aS33S24Vr;A1A2S20SeS0S0S49Vr;R2A2A3S9S9S9S23S0A2M0S0A2M1SbS9S9S0SfA2S23A2A1M2A2M3S0Lk;R2G1G2G1S0Lp0;R2G0S0G0S0Lp1;R2S23S0R1Llo;Ls;X9x1Lz;Lp1;X9x1Ll;Lp0;X9x1A2G3G2Lk;R2G1G2G1G2Lp0;R2G0S0G0G2Lp1;R2S23S0R5Lz0;Ls;X9x1Lz;Lp1;X9x1Lcs;Lp0;X9x1A4A2A2A2F_;Fk;").
Proof.
  intros k Hk. split; [exact (RCIV' k Hk)|]. pose proof (proj1 (Forall_forall _ _) ROSh_small k Hk) as SM. split; [exact SM|].
  split; [apply coverb_sound; exact (proj1 (forallb_forall _ _) ROSh_coverb k Hk)|].
  pose proof (LFRO r HEP k Hk) as LF. pose proof (RO_off k) as RO. destruct J2 as (_ & _ & _ & _ & _ & VK & _).
  destruct k as [[[b lo] hi] cs]. cbn [spec_range fst snd] in LF, RO |- *. destruct SM as (S1 & S2 & S3 & S4).
  unfold cells_in_view in LF |- *. apply Forall_forall. intros [[off kk] e] Hc j Hj.
  pose proof (proj1 (Forall_forall _ _) LF _ Hc j Hj) as X. cbn beta iota in X. rewrite <- X.
  pose proof (proj1 (Forall_forall _ _) S4 _ Hc) as CI. cbn beta iota in CI.
  set (z := bv_unsigned (eval r b) + lo - lo + off + Z.of_nat j).
  destruct (RO z Hk ltac:(unfold z; lia)) as [ND ZB].
  pose proof (VK z ND) as E. unfold vr in E. rewrite !view_in in E by lia. exact E.
Qed.
Lemma INRh : ltac2:(tb__ "0|4|
S30Q40M0A1S65Vr;VREST;R1A3S5S6S19S19S2S3cS19R1S35A3S2S1bSeS0S0S49Vr;R1A2M1A3S32G0R3A2M2A2S1cG2S11S0S0G1A3A2A2A2Lk;A2S2S1bS1dVT;Zad0A2S32G0R2A2M3A2S1cG3S1dVT;Zc60A2A2A2A2F_;Fa;").
Proof. intros a (o & Ho & Hr). exact (RCLS' o _ Ho Hr). Qed.
Lemma VO3 : ltac2:(tb__ "0|0|
S0S4S2S1bS1dVT;Zad0A2R1A2S1cR1S1dVT;Zc60A2A2A2A1S3S14S30Q8A1A1Vv3;R2A1Vvr;R2A1A3F_;Fz;").
Proof.
  intros z Hz. unfold v3, vr. destruct (Z_le_dec 0 z) as [L0|L0]; [destruct (Z_lt_dec z (2 ^ 64)) as [L1|L1]|].
  2,3: rewrite !view_out by lia; reflexivity.
  rewrite !view_in by lia.
  destruct (in_ranges_dec r REST (Z_to_bv 64 z)) as [Hin|Hout].
  - destruct (INRh _ Hin) as [(k & Hk & Hr)|Hc]; rewrite u64_lit in * by lia; [|exfalso; exact (Hz Hc)].
    unfold rho3. exact (absorb_specs_view r _ tr (vms md tpX ms) (vmd md) KEPT REST ROSh (rd_of segs (rm r)) Hsm1 OBJS NKr z k Hk Hr).
  - unfold rho3, rho_absorb, rd_of. cbn [rm]. destruct (in_ranges_dec r REST (Z_to_bv 64 z)) as [Hin'|]; [exfalso; exact (Hout Hin') | reflexivity].
Qed.
Lemma RMO3 : ltac2:(tb__ "0|0|
S30Q40A1S4S65Vr;VREST;R1A3A1S3S14S30Q8A1A1S24Vrho3;R2A2S24Vr;R2A2A3F_;Fa;").
Proof. intros a Hout. unfold rho3, rho_absorb. cbn [rm]. destruct (in_ranges_dec r REST a) as [Hin|]; [exfalso; exact (Hout Hin) | reflexivity]. Qed.
Lemma PRS3 : ltac2:(tb__ "0|3|
S0S4S3S14S30Q8A1M0A1M1Vvr;R1A1S16G0A1M2A3A1S4S3G1Vv3;R2A1G2A3A1F_;Fz;").
Proof.
  intros z Hd. unfold v3, vr in *. destruct (Z_le_dec 0 z) as [L0|L0]; [destruct (Z_lt_dec z (2 ^ 64)) as [L1|L1]|].
  2,3: rewrite view_out in Hd by lia; exfalso; apply Hd; reflexivity.
  destruct (in_ranges_dec r REST (Z_to_bv 64 z)) as [Hin|Hout].
  - destruct Hin as (o & Ho & Hr). rewrite u64_lit in Hr by lia.
    destruct (SpineMallocS9.absorb_obj r _ tr (vms md tpX ms) (vmd md) KEPT REST o Hsm1 OBJS Ho) as (_ & _ & X3 & _). cbn zeta in X3.
    unfold obj_range in Hr. cbn [fst snd] in Hr.
    destruct (X3 (or_introl (RUNK' o Ho)) (z - bv_unsigned (eval r (ob_base o))) ltac:(lia)) as [x Hx].
    unfold rho3. rewrite view_in by lia.
    replace (Z_to_bv 64 z) with (Z_to_bv 64 (bv_unsigned (eval r (ob_base o)) + (z - bv_unsigned (eval r (ob_base o))))) by (f_equal; lia).
    rewrite Hx. discriminate.
  - rewrite !view_in in * by lia. unfold rd_of in *. rewrite (RMO3 _ Hout). exact Hd.
Qed.

Lemma HA3 : ltac2:(tb__ "0|0|
S5bS33VA2;Vrho3;VtpX;Vmd;A5").
Proof.
  destruct J2 as (HA2 & HK & Htp & Htop & _ & _ & _).
  set (rK := rho_sets r [(156%positive, Z_to_bv 64 (ag_spacebeg G + kSpaceSize))]).
  assert (ERM : rm rK = rm r) by (unfold rK; apply rm_rho_sets).
  assert (OTH : forall v, v <> 156%positive -> rw rK v = rw r v) by (intros v Hv; unfold rK; rewrite rho_sets_other; [reflexivity | cbn; intros [E|[]]; congruence]).
  assert (HK0 : K0 Kc A2 rK tpX tr md).
  { split; [|split; [exact HK|split; [|split]]].
    - pose proof (AInvA_Q A2 r tpX md HA2) as HQ. unfold AInvQ in *. rewrite ERM. exact HQ.
    - unfold tp_ok in *. rewrite OTH by discriminate. exact Htp.
    - unfold top_high in *. unfold V_DEPTH in *. rewrite !OTH by discriminate. exact Htop.
    - unfold rigidQ. rewrite !OTH by discriminate. change (aa_geom A2) with G. split; [exact E151|]. split; [exact E152|]. split; [exact E155|].
      unfold rK. apply rho_sets_get; [cbn; repeat constructor; cbn; tauto | cbn; tauto]. }
  set (rK3 := mkVal (rw rK) (rl rK) (rm rho3)).
  assert (HK3 : K0 Kc A2 rK3 tpX tr md).
  { apply (kq_view segsA (K0 Kc) (K0_laws Kc HKc) A2 rK rK3 tpX tr md); [intros; reflexivity | intros; reflexivity | | | exact HK0].
    - intros z NQ. cbn [rm rK3]. rewrite ERM. apply VO3. intros Hz. apply NQ. right. right. unfold qstat_zone. change (aa_geom A2) with G. fold T. exact Hz.
    - intros z _ Hp. cbn [rm rK3]. rewrite ERM in Hp. exact (PRS3 z Hp). }
  destruct (AInvB_Q kQuarantineCacheMax A2 r tpX md HA2) as (HQ2 & QM & QB1 & QB2).
  assert (R5 : q_pure A2) by (destruct HQ2 as (_ & _ & _ & HRest & _); destruct HRest as (_ & _ & _ & _ & (R5 & _) & _); exact R5).
  pose proof (geomTI A2 r tpX md HA2) as TI. change (aa_geom A2) with G in TI. fold T in TI.
  assert (QM3 : q_mem (view segsA (rm rK3)) A2).
  { cbn [rm rK3]. apply (q_mem_frame A2 vr v3 R5); [| | | exact QM].
    - intros z Hz. apply VO3. intros Hs. apply (qfoot_offT A2 r tpX md HA2 z Hz). change (aa_geom A2) with G. fold T. lia.
    - intros z Hz. apply VO3. change (aa_geom A2) with G in Hz. fold T in Hz. lia.
    - intros z Hz. apply VO3. unfold QG in Hz. lia. }
  destruct (K0_back Kc A2 rK3 tpX tr md HK3 QM3 QB1 QB2) as (HA3' & _). exact HA3'.
Qed.

Lemma CLA : ltac2:(tb__ "0|0|
S0S7S3fVCST;VA;R1A3S3fVCST;VA';R1A3A2Fa;").
Proof. intros a. destruct HDO as (EG & _ & _ & _ & _ & EL & _ & _ & _ & EFB & _). unfold client_addrA, client_mut_addrA, aa_frames. rewrite EG, EL, EFB. tauto. Qed.
Lemma CLS : ltac2:(tb__ "0|0|
S0S7S40VCST;VXGL;VA;R1A4S40VCST;VXGL;VA';R1A4A2Fa;").
Proof. intros a. unfold client_shadowA. split; (intros [(x & Hx & E)|R]; [left; exists x; split; [apply CLA; exact Hx | exact E] | right; exact R]). Qed.
Lemma CLA2 : ltac2:(tb__ "0|0|
S0S3fVCST;VA2;R1A3S3fVCST;VA';R2A3F_;Fa;").
Proof.
  intros a Hc. unfold client_addrA, client_mut_addrA, aa_frames in *. change (aa_geom A2) with (aa_geom A') in Hc. change (aa_fs_busy A2) with (aa_fs_busy A') in Hc.
  change (aa_live A2) with (l1 ++ l2) in Hc. destruct Hc as [[S|[L|[FR|C]]]|FL]; [left; left; exact S | left; right; left | left; right; right; left; exact FR | left; right; right; right; exact C | right; exact FL].
  destruct L as (b & m & Hbm & Hx). exists b, m. split; [|exact Hx]. rewrite HLV. apply in_app_or in Hbm as [X|X]; apply in_or_app; [left; exact X | right; right; exact X].
Qed.
Lemma CLS2 : ltac2:(tb__ "0|0|
S0S40VCST;VXGL;VA2;R1A4S40VCST;VXGL;VA';R2A4F_;Fa;").
Proof. intros a [(x & Hx & E)|R]; [left; exists x; split; [exact (CLA2 x Hx) | exact E] | right; exact R]. Qed.

Lemma A2parts : ltac2:(tb__ "0|0|
S2S60S6eS5fVG;A1Vvr;A2VA2;A2S62VA2;A1A2").
Proof. destruct J2 as (HA2 & _). destruct HA2 as (_ & _ & HF & (Hsep & _) & _). exact (conj HF Hsep). Qed.

Lemma client_off_REST : ltac2:(tb__ "0|2|
S30Q40M0A1S5S3fVCST;VA2;S32G0R1A2M1A3S40VCST;VXGL;VA2;G1A4A2S4S65Vr;VREST;R2A3A1F_;Fa;").
Proof.
  intros a Hcl Hin. destruct A2parts as (HF & Hsep). pose proof HG2 as HG.
  pose proof (geom_bands _ HG) as (WF & TB' & CB & DB & _). fold T in TB'. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB', CB, DB.
  assert (ZON : (0 <= bv_unsigned a < IMG_HI) \/ (T <= bv_unsigned a < T + 0x1000) \/ (ag_ctx G <= bv_unsigned a < ag_ctx G + 0x1000)).
  { destruct (INRh a Hin) as [(k & Hk & Hr)|Hs]; [|right; left; lia].
    destruct (ROSh_zone G r k _ HG E151 E152 B12 Hk Hr) as [[Z1 _]|[Z1|Z1]]; [left; exact Z1 | right; left; exact Z1 | right; right; exact Z1]. }
  destruct Hcl as [Hc|Hs].
  -
    destruct ZON as [ZI|ZT].
    + destruct (client_addr_cases CST A2 _ _ HF Hc) as [S|[L|[FR|[C|FL]]]]; change (aa_geom A2) with G in *.
      * pose proof (topG_range G). unfold IMG_HI in ZI. lia.
      * destruct L as (b & m & Hbm & Hx). destruct (Hsep b m Hbm) as (S1 & S2 & _). unfold IMG_HI in *. lia.
      * destruct FR as (c & p0 & Hc0 & Hp & _ & Hx). pose proof (fs_geom_nums G c p0 HG Hc0 Hp) as M. cbn zeta in M.
        rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. pose proof (geom_numsS _ HG) as (_ & F1 & _). unfold IMG_HI in *. lia.
      * destruct (INRh a Hin) as [(k & Hk & Hr)|Hs]; [|pose proof (geom_numsS _ HG) as (_ & _ & _ & G4 & G5 & _); fold T in G4, G5;
            destruct (HCST _ C) as [X _]; pose proof (geomTI A2 r tpX md (proj1 J2)) as TI; change (aa_geom A2) with G in TI; fold T in TI; unfold IMG_LO, IMG_HI in *; lia].
        unfold ROSh in Hk. apply in_app_or in Hk as [Hk|Hk].
        -- pose proof (NRTX_zone G r k _ HG E151 E152 B12 Hk Hr) as [R|R]; [|exact (HCSTF _ C R)].
           exact (client_not_rt CST HCST A2 _ _ HG HF Hsep Hc R).
        -- apply (HNQ _ (CLA2 _ Hc)). apply in_app_or in Hk as [Hk|Hk].
           ++ unfold N_hb in Hk. cbn [firstn In] in Hk. right. unfold qrtc_zone, SEC_INST in *.
              destruct Hk as [<-|[<-|[<-|[]]]]; cbn [spec_range fst snd eval] in Hr; rewrite u64_lit in Hr by lia.
              ** left. lia.
              ** left. lia.
              ** exfalso. apply (HNQ _ (CLA2 _ Hc)). left. right. right. right. left. unfold SEC_INST. lia.
           ++ destruct Hk as [<-|[]]. left. left. right. left. unfold qhdr_zone. left.
              cbn [spec_range fst snd qsz_spec] in Hr. pose proof EvT as ET. unfold cQ in Hr. cbn [eval] in Hr. rewrite add_val, u64_lit in Hr by lia.
              change (rw r 151%positive) with (eval r vT) in Hr. rewrite ET in Hr. pose proof (geom_numsS _ HG) as (_ & _ & _ & G4 & G5 & _). pose proof (topG_range G). fold T in G4, G5.
              rewrite Z.mod_small in Hr by lia. change (aa_geom A') with G. fold T. lia.
      * destruct FL as (c & p0 & Hc0 & Hp & _ & E). pose proof (fs_geom_nums G c p0 HG Hc0 Hp) as M. cbn zeta in M.
        rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold fs_flags in *. rewrite FS_kFlagsOffset_val in *. pose proof (geom_numsS _ HG) as (_ & F1 & _). unfold IMG_HI in *. lia.
    + apply (client_not_rt CST HCST A2 _ _ HG HF Hsep Hc). unfold rt_zone. change (aa_geom A2) with G. fold T. right. destruct ZT as [ZT|ZT]; [left; exact ZT | right; left; exact ZT].
  -
    pose proof (client_shadow_bounds CST XGL HCST HXGL A2 _ _ HG HF Hsep Hs) as B. unfold SHADOW_OFF, HIGH_SHADOW_END in B.
    unfold IMG_HI in ZON. fold T in TB'. lia.
Qed.

Lemma client_off_TZ : ltac2:(tb__ "0|0|
S0S5S3fVCST;VA2;R1A3S40VCST;VXGL;VA2;R1A4A2S4S36VA';Vch;R2A3A1F_;Fa;").
Proof.
  intros a Hcl HT. destruct A2parts as (HF & Hsep). pose proof HG2 as HG.
  destruct CHB as (C1 & C2 & C3 & C4 & C5 & C6). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in C6.
  assert (SHZ : forall z, chunk_sh_zone ch z -> 2147446784 <= z < 17594333495296).
  { intros z Hz. unfold chunk_sh_zone in Hz. fold h msz in Hz. unfold IMG_HI in C3.
    pose proof (Z.div_pos h 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (h + msz) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). unfold Sh, SHADOW_OFF in Hz. lia. }
  destruct Hcl as [Hc|Hs].
  - destruct HT as [HQ|[HC|HS]]; [exact (HNQ _ (CLA2 _ Hc) HQ) | exact (HNOC _ Hc HC)|].
    destruct (client_addr_bounds CST HCST A2 a _ HG HF Hsep Hc) as [_ B]. pose proof (SHZ a HS). lia.
  - destruct HT as [HQ|[HC|HS]]; [exact (HNQS _ (CLS2 _ Hs) HQ)| |].
    + pose proof (client_shadow_bounds CST XGL HCST HXGL A2 a _ HG HF Hsep Hs) as B. unfold SHADOW_OFF, HIGH_SHADOW_END in B. unfold chunk_zone in HC. fold h msz in HC. lia.
    +
      destruct (proj1 (Z.mod_divide h 8 ltac:(lia)) C1) as [u Hu]. destruct (proj1 (Z.mod_divide (h + msz) 8 ltac:(lia)) ltac:(rewrite Z.add_mod, C1, C2 by lia; reflexivity)) as [u2 Hu2].
      unfold chunk_sh_zone in HS. fold h msz in HS. unfold Sh in HS. rewrite Hu2 in HS. rewrite Hu in HS. rewrite !Z.div_mul in HS by lia.
      assert (INCH : forall y, a = Sh y -> chunk_zone ch y).
      { intros y ->. unfold Sh in HS. pose proof (Z.div_mod y 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound y 8 ltac:(lia)) as MB. unfold chunk_zone. fold h msz. lia. }
      destruct Hs as [(y & Cy & Ey)|(y & Gy & Ey)].
      * exact (HNOC y Cy (INCH y Ey)).
      * destruct (HXGL y Gy) as [Y1 Y2]. pose proof (INCH y Ey) as X. unfold chunk_zone in X. fold h msz in X. unfold IMG_HI in *. lia.
Qed.

Lemma HKEPT : ltac2:(tb__ "0|0|
S46VCST;VXGL;VA;VA2;S24Vrho;A1S24Vrho3;A1A6").
Proof.
  destruct J2 as (HA2 & _ & _ & _ & KEY & _ & PR). destruct A2parts as (HF & Hsep). pose proof HG2 as HG.
  destruct HLK as (_ & _ & Lm & Ld). assert (Erm1 : rm rho1 = rm rho) by (unfold rho1, rhoF_of; apply rm_rho_sets).
  split.
  - intros a Ha Hcl.
    assert (C2 : client_addrA CST A2 a \/ client_shadowA CST XGL A2 a) by (destruct Hcl as [(_ & X & _)|(_ & X & _)]; [left; exact X | right; exact X]).
    assert (C0 : client_addrA CST A a \/ client_shadowA CST XGL A a) by (destruct Hcl as [(X & _ & _)|(X & _ & _)]; [left; exact X | right; exact X]).
    rewrite RMO3 by (apply client_off_REST; rewrite u64_lit by lia; exact C2).
    rewrite KEY by (rewrite u64_lit by lia; exact (client_off_TZ a C2)).
    rewrite (Lm (Z_to_bv 64 a)) by (rewrite u64_lit by lia; exact (HKEEP a C0)). rewrite Erm1. reflexivity.
  - intros x j Hx Hj Hdef.
    assert (Bx : 0 <= x < 2 ^ 47).
    { destruct Hx as [[_ CX]|GX]; [exact (proj1 (client_addr_bounds CST HCST A2 x _ HG HF Hsep CX))|]. destruct (HXGL x GX) as [X1 X2]. unfold IMG_HI in X2. lia. }
    destruct (word_byte_range (Sh x) j ltac:(unfold Sh, SHADOW_OFF; lia) Hj) as (W1 & W2 & W3).
    assert (BAND : SHADOW_BAND_LO <= bv_unsigned (word_byte (Sh x) j) < SHADOW_BAND_HI).
    { rewrite W2. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, Sh, SHADOW_OFF in *.
      pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
    set (a := word_byte (Sh x) j) in *.
    assert (D1 : rm rho1' a <> None) by (apply Ld; [exact BAND | rewrite Erm1; exact Hdef]).
    assert (NIR : ~ in_ranges r REST a).
    { intros Hin. pose proof (geom_bands _ HG) as (WF & TB' & CB & DB & _). fold T in TB'. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
      destruct (INRh a Hin) as [(k & Hk & Hr)|Hs]; [|lia].
      destruct (ROSh_zone G r k _ HG E151 E152 B12 Hk Hr) as [[Z1 _]|[Z1|Z1]]; unfold IMG_HI in *; try (fold T in Z1); lia. }
    rewrite (RMO3 a NIR).
    assert (Ua : 0 <= bv_unsigned a < 2 ^ 64) by (pose proof (bv_unsigned_in_range _ a) as X; change (bv_modulus 64) with (2 ^ 64) in X; exact X).
    assert (HI : IMG_HI <= bv_unsigned a) by (unfold SHADOW_BAND_LO, LOW_SHADOW_BEG, IMG_HI in *; lia).
    pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.RebuildR.view_rm_off (rm rho1') _ Ua (or_intror HI)) as VR1. change InvLaws.segsA with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA in VR1. rewrite Z_to_bv_bv_unsigned in VR1.
    pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.RebuildR.view_rm_off (rm r) _ Ua (or_intror HI)) as VR2. change InvLaws.segsA with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA in VR2. rewrite Z_to_bv_bv_unsigned in VR2.
    assert (V1 : view segs (rm rho1') (bv_unsigned a) <> None) by (rewrite VR1; exact D1).
    assert (NCZ : ~ chunk_zone ch (bv_unsigned a)).
    { destruct CHB as (_ & _ & C3 & C4 & C5 & C6). unfold chunk_zone. fold h msz. lia. }
    pose proof (PR _ NCZ V1) as V2. unfold vr in V2. rewrite VR2 in V2. exact V2.
Qed.

Theorem hb_finish : ltac2:(tb__ "0|1|
S5aS33S76Vrho;Vtp;SaS9S56S59A2M0ScS56S59S44S42VW;S41A3S43S5bS33A1VCST;VXGL;VA;VKc;A5A4S10G0A1A3Vw;A6").
Proof.
  destruct J2 as (HA2 & HK & Htp & _). pose proof HG2 as HG.
  assert (Hc : SPA segs KJ XR rho3 tpX w).
  { unfold XR. rewrite <- (x_EQR nW XF XOK). eapply SPA_restate; [exact (x_WXR nW XF XOK) | exact (x_DXR nW XF XOK) | exact (x_NXR nW XF XOK) | | constructor | exact Hb].
    constructor; [|constructor]. cbn [fst snd eval]. unfold tp_ok in Htp. apply bv_eq. rewrite u64_lit by (unfold TP_A; lia).
    unfold rho3. cbn [rho_absorb rw]. rewrite Htp. change (aa_geom A2) with G. destruct (geom_old _ HG) as (_ & _ & _ & G4 & _). rewrite G4. reflexivity. }
  pose proof (smatchA_entails segs _ _ _ rho3 tpX _ (x_ENT nW XF XOK) (proj1 Hc)) as Hsm4.
  set (rho4 := rho_sub rho3 sX) in Hsm4.
  assert (Hlow : forall k, (k < NF)%positive -> rw rho4 k = rw r k).
  { intros k Hk. unfold rho4, sX. cbn [rho_sub rw]. rewrite (wsub_get_id _ _ _ (x_SID nW XF XOK) Hk). reflexivity. }
  assert (Erm4 : rm rho4 = rm rho3) by exact (rm_rho_sub' rho3 sX).
  destruct HR as [[AGw AGl] _ _ _ _ _ _ _ _ _]. destruct HLK as (Lw & Ll & _).
  exists (L_free AE_A W UStopLe), (JL_free (AInvA segs) CST XGL A Kc), rho4, tpX.
  split; [left; reflexivity|]. split; [|split; [exact Hsm4|]].
  { split.
    - intros k Hk. rewrite (Hlow k Hk), (proj1 HEP k) by (unfold NF, GW in *; lia). rewrite Lw. exact (AGw k Hk).
    - intros l. unfold rho4, rho3. cbn [rl rho_sub rho_absorb]. rewrite (proj1 (proj2 HEP) l), Ll. exact (AGl l). }
  cbn [w_tr w_cfg cfg_model fst snd]. unfold JL_free. exists A2, l1, l2.
  destruct HDO as (EG & EC & ECI & ESEC & EPC & EL & EQT & EQG & EII & EFB & EFH & EV & EKM & EKF).
  split; [pose proof HA3 as X; unfold AInvA in *; rewrite Erm4; exact X|].
  split; [rewrite Hp12, Hn13, <- EL; exact HLV|].
  split; [reflexivity|]. split; [unfold aa_frames; change (aa_fs_busy A2) with (aa_fs_busy A'); rewrite EFB; reflexivity|].
  split; [exact EV|]. split; [exact EKM|]. split; [exact EKF|]. split; [exact EG|].
  split; [rewrite Erm4; exact HKEPT|]. split; [exact HK|].
  intros c Hc0 NE Hfr. unfold class_fresh in *. change (aa_cls A2) with (aa_cls A'). rewrite EC. exact Hfr.
Qed.
End FINH.

Theorem G_exit : ltac2:(tb__ "0|3|
S25SbS30Q40M0A1M1A1S83S3G1S22R3Pc3A2S31G0S1dS50VG;A1S69A2A2A3S3G1S22R4Pc8A2S31G0S51VG;A1A2A3S55S33S4eVKc;VA';Vrho1';Vl1;Vl2;Vi;Vch;S36VA';Vch;A2A8VXF;R5R4R3A6S5aS33S76Vrho;Vtp;SaS9S56S59A2M2ScS56S59S44S42VW;S41A3S43S5bS33A1VCST;VXGL;VA;VKc;A5A4S10G2A1A3R4A6F_;F_;F_;Fw;FtpX;Fr;").
Proof.
  intros r tpX [tr [ms md]] E195 E200 H.
  assert (HEP : EXPIN r).
  { destruct H as [_ (_ & _ & _ & _ & RW & RL & _)]. split; [exact RW|]. split; [exact RL|]. split; [exact E195 | exact E200]. }
  exact (hb_finish r tpX tr ms md HEP H).
Qed.
End ExitH.
End F0A_hbN_exit.

