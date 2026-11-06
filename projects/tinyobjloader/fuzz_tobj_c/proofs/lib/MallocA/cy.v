(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cw ct.
From Stdlib Require Permutation FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c9 ci dc dt.

(* [comment removed for export] *)
Module SpineCallocSecOK0.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.SpineCallocSecI"; "st0"; "W0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@Corelib.Init.Datatypes"; "list"; "false"; "prod"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "PFc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "@Corelib.Init.Logic"; "False"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "ES1g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "JGsC"; "clsP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "vm_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1"; "E_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2"; "IMG_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3I"; "nx0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IL"; "nx0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec4I.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec4IL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ct.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CertCallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SecRoom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.CSecLinks OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.SpineCallocSecOK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.SpineCallocSecI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec4I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineCallocSec5I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cf.SpineCallocSec5J OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cw.SpineCallocSec6J OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec4IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineCallocSec5IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cf.SpineCallocSec5JL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ct.SpineCallocSec6JL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section OK0.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S10SdVCST;R1A2SdS25R2A2S19F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S10SdVCST;R1A2SdS27R2A2S19F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S10SdVCST;R1A2S1bS26R2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Hypothesis law_res : ltac2:(tb__ "0|1|
S8S3S9SeQ40A1M0A1S21VAInv;R4R3R2R1A4S1aS9SbG0G0A2A1S23S22R2A1A1S20S0A1A3F_;Fmd;Ftp;Frho;FA;").

Theorem sec_ok_0h : ltac2:(tb__ "0|2|
S12OF_;S8S17S3SeQ40M0A1M1S9G1A1S18R4A1S7S0R7S5R5A1A3S15S0R8S5R6A1A3S1eScSfG0R5A2S1fSfG0S4R6PcA2A2A1A3S3S11S0RbS6S0S1dU0S1S28S8R1LX;RaR9R8R7A8S1cS2S1Z2A3R1R6A5S14S0S13R8R6S16VCST;VXGL;S2S1RaR9A6A5A4FrhoX;F_;F_;F_;F_;Ftp;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a tp HKc Hokl Hokpl HC rhoX.
  exact (sec_ok_chain 0%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3I.nx0 true CST XGL HCST HXGL HCSTS HCSTD (ES1g W0 st0 2)
           OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3I.D2c SpineCallocSec4I.T4ac SpineCallocSec4I.T4bc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineCallocSec5I.C5ac OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineCallocSec5I.C5bc
           sec_g12_0h sec_g3_0h sec_g41_0ha sec_g41_0hb (sec_tail_0ha CST XGL HCST HXGL HCSTM HCSTS) (sec_tail_0hb CST XGL HCST HXGL HCSTM HCSTS)
           ok A Kc rho a tp ltac:(hw_discharge) (stopJ_stable_le _) HKc Hokl Hokpl HC rhoX).
Qed.

Theorem sec_ok_0l : ltac2:(tb__ "0|2|
S12OF_;S8S17S3SeQ40M0A1M1S9G1A1S18R4A1S7S0R7S5R5A1A3S15S0R8S5R6A1A3S1eSaSfG0R5A2S1fSfG0S4R6PcA2A2A1A3S3S11S0RbS6S0S1dU0S1S29S8R1LX;RaR9R8R7A8S1cS2S1Z2A3R1R6A5S14S0S13R8R6S16VCST;VXGL;S2S1RaR9A6A5A4FrhoX;F_;F_;F_;F_;Ftp;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a tp HKc Hokl Hokpl HC rhoX.
  exact (sec_ok_chain 0%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IL.nx0 false CST XGL HCST HXGL HCSTS HCSTD (ES1g W0 st0 2)
           OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IL.D2c SpineCallocSec4IL.T4ac SpineCallocSec4IL.T4bc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineCallocSec5IL.C5ac OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineCallocSec5IL.C5bc
           sec_g12_0l sec_g3_0l sec_g41_0la sec_g41_0lb (sec_tail_0la CST XGL HCST HXGL HCSTM HCSTS) (sec_tail_0lb CST XGL HCST HXGL HCSTM HCSTS)
           ok A Kc rho a tp ltac:(hw_discharge) (stopJ_stable_le _) HKc Hokl Hokpl HC rhoX).
Qed.

Theorem calloc_sec_ok_0 : ltac2:(tb__ "0|0|
S12OF_;S8S17S3S9SeQ40A1A1S18R3A1S7Vsegs;R6S5R4A1A3S15Vsegs;R7S5R5A1A3S3S11Vsegs;R9S6Vsegs;S2aS2S1R8R7R6A5S24S2S1Z2Z8A4R1R5A5S14Vsegs;S13R6R5S16VCST;VXGL;S2S1R8R7A6A5A4FrhoE;F_;F_;F_;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp HKc Hokl Hokpl rhoE.
  apply (calloc_sec_0 CST XGL HCST HXGL HCSTM HCSTS law_res ok A Kc
           (fun a => OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.JGsC 0%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3I.nx0 (fun X : AA => X) A Kc rho a) rho tp HKc Hokl Hokpl).
  - intros rhoX tr ms md a Hsp HJG Hpl. rewrite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.SpineCallocSecI.NX1_0.
    exact (grant_Jo 0%nat st0 2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3I.nx0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3I.Hnx_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3I.NXG_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.SpineCallocSecI.R11_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.SpineCallocSecI.FC1_0 A Kc rho rhoX tp tr ms md a (stopJ_stable_le _) HKc Hsp HJG Hpl).
  - intros rhoX a. change (nxS W0 st0 2) with (nxS (Wcan 0) UStopLe 2). rewrite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3I.Hnx_0.
    apply (cls_split 0%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3I.nx0 ok A Kc rho a (ES1g W0 st0 2) _ tp).
    + intros HC. exact (sec_ok_0h ok A Kc rho a tp HKc Hokl Hokpl HC _).
    + intros HC. exact (sec_ok_0l ok A Kc rho a tp HKc Hokl Hokpl HC _).
Qed.
End OK0.
End SpineCallocSecOK0.

(* [comment removed for export] *)
Module SpineCallocSecOK0W1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.SpineCallocSecIW1"; "st0"; "W0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@Corelib.Init.Datatypes"; "list"; "false"; "prod"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "PFc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "@Corelib.Init.Logic"; "False"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "ES1g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "JGsC"; "clsP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "vm_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1"; "E_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2"; "IMG_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3ILW1"; "nx0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IW1"; "nx0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec4IW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec4ILW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require co.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ct.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CertCallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SecRoom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.CSecLinks OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.SpineCallocSecOK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.SpineCallocSecIW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec4IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineCallocSec5IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cq.SpineCallocSec5JW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cw.SpineCallocSec6JW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3ILW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec4ILW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.co.SpineCallocSec5ILW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cf.SpineCallocSec5JLW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ct.SpineCallocSec6JLW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section OK0.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S10SdVCST;R1A2SdS25R2A2S19F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S10SdVCST;R1A2SdS27R2A2S19F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S10SdVCST;R1A2S1bS26R2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Hypothesis law_res : ltac2:(tb__ "0|1|
S8S3S9SeQ40A1M0A1S21VAInv;R4R3R2R1A4S1aS9SbG0G0A2A1S23S22R2A1A1S20S0A1A3F_;Fmd;Ftp;Frho;FA;").

Theorem sec_ok_1h : ltac2:(tb__ "0|2|
S12OF_;S8S17S3SeQ40M0A1M1S9G1A1S18R4A1S7S0R7S5R5A1A3S15S0R8S5R6A1A3S1eScSfG0R5A2S1fSfG0S4R6PcA2A2A1A3S3S11S0RbS6S0S1dU1S1S29S8R1LX;RaR9R8R7A8S1cS2S1Z3A3R1R6A5S14S0S13R8R6S16VCST;VXGL;S2S1RaR9A6A5A4FrhoX;F_;F_;F_;F_;Ftp;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a tp HKc Hokl Hokpl HC rhoX.
  exact (sec_ok_chain 1%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IW1.nx0 true CST XGL HCST HXGL HCSTS HCSTD (ES1g W0 st0 3)
           OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IW1.D2c SpineCallocSec4IW1.T4ac SpineCallocSec4IW1.T4bc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineCallocSec5IW1.C5ac OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineCallocSec5IW1.C5bc
           sec_g12_1h sec_g3_1h sec_g41_1ha sec_g41_1hb (sec_tail_1ha CST XGL HCST HXGL HCSTM HCSTS) (sec_tail_1hb CST XGL HCST HXGL HCSTM HCSTS)
           ok A Kc rho a tp ltac:(hw_discharge) (stopJ_w_stable _ _ stopJ_w_1pc) HKc Hokl Hokpl HC rhoX).
Qed.

Theorem sec_ok_1l : ltac2:(tb__ "0|2|
S12OF_;S8S17S3SeQ40M0A1M1S9G1A1S18R4A1S7S0R7S5R5A1A3S15S0R8S5R6A1A3S1eSaSfG0R5A2S1fSfG0S4R6PcA2A2A1A3S3S11S0RbS6S0S1dU1S1S28S8R1LX;RaR9R8R7A8S1cS2S1Z3A3R1R6A5S14S0S13R8R6S16VCST;VXGL;S2S1RaR9A6A5A4FrhoX;F_;F_;F_;F_;Ftp;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a tp HKc Hokl Hokpl HC rhoX.
  exact (sec_ok_chain 1%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3ILW1.nx0 false CST XGL HCST HXGL HCSTS HCSTD (ES1g W0 st0 3)
           OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3ILW1.D2c SpineCallocSec4ILW1.T4ac SpineCallocSec4ILW1.T4bc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.co.SpineCallocSec5ILW1.C5ac OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.co.SpineCallocSec5ILW1.C5bc
           sec_g12_1l sec_g3_1l sec_g41_1la sec_g41_1lb (sec_tail_1la CST XGL HCST HXGL HCSTM HCSTS) (sec_tail_1lb CST XGL HCST HXGL HCSTM HCSTS)
           ok A Kc rho a tp ltac:(hw_discharge) (stopJ_w_stable _ _ stopJ_w_1pc) HKc Hokl Hokpl HC rhoX).
Qed.

Theorem calloc_sec_ok_1 : ltac2:(tb__ "0|0|
S12OF_;S8S17S3S9SeQ40A1A1S18R3A1S7Vsegs;R6S5R4A1A3S15Vsegs;R7S5R5A1A3S3S11Vsegs;R9S6Vsegs;S2aS2S1R8R7R6A5S24S2S1Z3Z8A4R1R5A5S14Vsegs;S13R6R5S16VCST;VXGL;S2S1R8R7A6A5A4FrhoE;F_;F_;F_;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp HKc Hokl Hokpl rhoE.
  apply (calloc_sec_1 CST XGL HCST HXGL HCSTM HCSTS law_res ok A Kc
           (fun a => OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.JGsC 1%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IW1.nx0 (fun X : AA => X) A Kc rho a) rho tp HKc Hokl Hokpl).
  - intros rhoX tr ms md a Hsp HJG Hpl. rewrite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.SpineCallocSecIW1.NX1_0.
    exact (grant_Jo 1%nat st0 3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IW1.nx0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IW1.Hnx_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IW1.NXG_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.SpineCallocSecIW1.R11_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.SpineCallocSecIW1.FC1_0 A Kc rho rhoX tp tr ms md a (stopJ_w_stable _ _ stopJ_w_1pc) HKc Hsp HJG Hpl).
  - intros rhoX a. change (nxS W0 st0 3) with (nxS (Wcan 1) UStopLeOrPc 3). rewrite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IW1.Hnx_0.
    apply (cls_split 1%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IW1.nx0 ok A Kc rho a (ES1g W0 st0 3) _ tp).
    + intros HC. exact (sec_ok_1h ok A Kc rho a tp HKc Hokl Hokpl HC _).
    + intros HC. exact (sec_ok_1l ok A Kc rho a tp HKc Hokl Hokpl HC _).
Qed.
End OK0.
End SpineCallocSecOK0W1.

(* [comment removed for export] *)
Module F0A_hbN_scan.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "iff"; "ex"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "sec_chunk"; "aa_sec"; "sc_map_beg"; "sc_map_size"; "aa_geom"; "ag_spacebeg"; "ag_ctx"; "ag_pab"; "ag_thread"; "topG"; "AA"; "ageom"; "sc_size"; "@Corelib.Init.Datatypes"; "nat"; "bool"; "cons"; "true"; "length"; "list"; "Some"; "option"; "nil"; "pair"; "prod"; "false"; "S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "sobj"; "eval"; "sprop"; "sv"; "ss_objs"; "holds"; "rl"; "rm"; "ss_facts"; "SVar"; "sprop_below"; "sprop_eqb"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "of_nat"; "mul"; "lt"; "pow"; "div"; "sub"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cy.F0A_hbN_scan"; "PIN0"; "chsep"; "zbLh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "GW"; "@Stdlib.Lists.List"; "nth_error"; "In"; "Forall2"; "forallb"; "existsb"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_env"; "hbenv"; "@Corelib.Init.Peano"; "lt"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue"; "zloS"; "fam_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SegQS_loop"; "zhiX"; "ZUXl"; "zbE"; "SCANI"; "XVALS"; "UX"; "ZDU"; "a3_of"; "NX"; "ZDNX"; "NSC"; "zbX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones"; "zdesc"; "in_zone"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cw.F0A_hbN_scand"; "lfh"; "ZULh"; "hbscanV_ok"; "LFh"; "lastb"; "FCHs"; "F2Xh"; "Ld_hb"; "Lx_hb"; "T_exit_hb"; "T_first_hb"; "T_loop_hb"; "hbscanF_ok"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.F0A_hbN_zones"; "in_zoneW"; "zd_allb"; "zenv"; "zds_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kPtrArrayReserve"; "IMG_HI"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kSpaceSize"; "LOW_SHADOW_BEG"; "PG"; "round_up"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states"; "vCHV"; "vPTR"; "vH"; "O_chS"; "OBJ2"; "sel_last"; "vEND"; "vNEAR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert"; "hf_LA"; "hf_SC"; "VSCh"; "hv_SX"; "hbfam"; "hbvar"; "hf_lPL"; "VS0h"; "VSXh"; "hbfam_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cy.F0A_hbN_scan.LoopH"; "FCH1"; "ENVXs"; "ENV0s"; "hbnums"; "XVALSh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM"; "idm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM"; "keepsM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr"; "TR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue"; "dropN"; "dspec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4"; "chunk_sh_zone";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cy.F0A_hbN_scan.EnvH"; "zbLh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws"; "N8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "O_sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "Wcan"; "top_high"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cell_ok"; "mkACell"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip"; "carve_okq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib"; "s_ok"; "s_okU"; "unk_ok"; "uobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_blind"; "JW"; "blind_rel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states"; "mT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_hbN_step"; "ro_condW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_scan"; "best"; "upd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "stopJ_stable"; "@Stdlib.Arith.PeanoNat.Nat"; "even"; "@Stdlib.PArith.BinPos.Pos"; "lt"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQS_glue SegQS_scan SegQS_lib.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cw.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.InvQ10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.SegQS_k OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_blind OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.F0A_hbN_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_hbN_step OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_entry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c9.F0A_hbN_stepU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cw.F0A_hbN_scand.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma upd_of_leaf_h : ltac2:(tb__ "0|4|
S20S13S38S38S38S47R4U8A2S0S37Q40M0A1M1S23R6SaeA2S36G0R4A2A3S0G1S23R7S79A2S36G0R3A2A3S0G1S23R8S80A2S36G0R5A2A3S1S2eZ0M2R6A2S2eR6R7A2A2S32R8S33Z2Z40A2M3A2S1S2eG2R7A2S32R7G3A2A2S6aS24S27RcA1S60RbA1A3S0G1S23RdS52RcA1A2S36G0Sb3RbRaR9A3A2A3F_;F_;F_;F_;F_;F_;F_;F_;Fc;Fnr;Fpp;Fk;Frho;").
Proof.
  intros rho k pp nr c Hk Ep Ec En Hn Hp Hc HF. unfold LFh in HF.
  apply Forall_cons_iff in HF as [_ HF]. apply Forall_cons_iff in HF as [F1 HF]. apply Forall_cons_iff in HF as [F2 _].
  assert (S1 : bv_unsigned (eval rho (SAlu ALU_SUB mT vCHV)) = (pp - c) mod 2 ^ 64) by (apply U_sub; [exact Ep | exact Ec | lia | lia]).
  assert (S2 : bv_unsigned (eval rho (SAlu ALU_SUB mT vNEAR)) = (pp - nr) mod 2 ^ 64) by (apply U_sub; [exact Ep | exact En | lia | lia]).
  assert (L1 : holds rho LT1h <-> pp < c).
  { unfold LT1h. cbn [holds branch_taken]. unfold bv_ltu. rewrite Ep, Ec, !u64_lit by lia. apply Z.ltb_lt. }
  assert (L2 : holds rho LT2h <-> (pp - c) mod 2 ^ 64 < (pp - nr) mod 2 ^ 64).
  { unfold LT2h. cbn [holds branch_taken]. unfold bv_ltu. rewrite S1, S2. apply Z.ltb_lt. }
  destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [| | | | | | | | exfalso; lia]; cbn [Nat.ltb Nat.leb Nat.modulo Nat.divmod fst snd Nat.sub] in F1, F2; cbn [a3_of].
  - rewrite En, (upd_no_lt pp nr c (proj1 L1 F1)). reflexivity.
  - rewrite En, (upd_no_lt pp nr c (proj1 L1 F1)). reflexivity.
  - rewrite Ec, (upd_yes pp nr c Hn Hp Hc (proj1 L2 F2) (fun H => F1 (proj2 L1 H))). reflexivity.
  - rewrite Ec, (upd_yes pp nr c Hn Hp Hc (proj1 L2 F2) (fun H => F1 (proj2 L1 H))). reflexivity.
  - rewrite En, (upd_no_lt pp nr c (proj1 L1 F1)). reflexivity.
  - rewrite En, (upd_no_lt pp nr c (proj1 L1 F1)). reflexivity.
  - rewrite En, (upd_no_ge pp nr c Hn Hp Hc (fun H => F2 (proj2 L2 H))). reflexivity.
  - rewrite En, (upd_no_ge pp nr c Hn Hp Hc (fun H => F2 (proj2 L2 H))). reflexivity.
Qed.

Section EnvH.
Variables (A : AA) (it : Z * Z) (i : nat) (ch : sec_chunk).
Let G : ageom := aa_geom A.
Let T : Z := ag_thread G.
Let CTX : Z := ag_ctx G.
Let PAB : Z := ag_pab G.
Let h : Z := sc_map_beg ch.
Let ms : Z := sc_map_size ch.
Let NC : Z := Z.of_nat (length (aa_sec A)).
Definition zbLh (c9 : Z) : nat -> Z := ltac2:(tb__ "0|1|
S56VT;VCTX;SfVG;A1Vh;S76Z0M0G0G0Vc9;A9").

Lemma tbl_nums_h: ltac2:(tb__ "0|2|
S20S46VA;Vit;Vi;Vch;R1A5S1S2eS72VPAB;A2S1S2eS2fVPAB;S71A2M0SfVG;A1A2S1S2eS31Z8VNC;A2S71A2S1S2S2eG0S74A2S2eS73VPAB;A2A2S1S2S2eG0VT;A2S2eS2fVT;Z1000M1A2VPAB;A2A2S1S2S2eG0VCTX;A2S2eS2fVCTX;G1A2VPAB;A2A2S2S2eS2fVh;Vms;A2VPAB;A2S2eG0Vh;A2A2A2A2A2A2A2A2F_;Frho;").
Proof.
  intros rho [HG HSEP3 _ _ HSR _ _ _ HSEP _ _ _ _].
  destruct HSR as (_ & _ & (B1 & B2) & _ & PD & _). pose proof (dyn_ok_big _ _ _ PD ltac:(unfold kPtrArrayReserve; lia)) as BIG.
  destruct PD as (_ & _ & _ & P3 & _ & P5). destruct HSEP3 as (_ & _ & _ & _ & ST & _ & SC & _). destruct HSEP as (_ & _ & HP & _).
  clear HG. unfold NC, PAB, T, CTX, G, h, ms in *.
  split; [exact BIG|]. split; [exact P3|]. split; [clear -B1 B2; lia|]. split; [exact P5|]. split; [exact ST|]. split; [exact SC | exact HP].
Qed.

Lemma zsepLh : ltac2:(tb__ "0|3|
S20S38S46VA;Vit;Vi;Vch;R2A5S2eVPAB;R2A2S2eS2fR3Z8A2S2fVPAB;S71A2A2S13S13S40S13R2S5eA3M0G0S5S0S13R4R3A3A1S2S2eS2fS9eR9R5A2M1S4bVms;R5A2A2S2fS9eR9R4A2M2S49R4A1A2A2S2eS2fG2S4bVms;R4A2A2S2fG1S49R5A1A2A2A2F_;F_;F_;Fz';Fz;F_;F_;F_;Fc9;Frho;").
Proof.
  intros rho c9 QS C1 C2. pose proof (tbl_nums_h rho QS) as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  pose proof (qs_nums A it i ch rho QS) as (T0 & T1 & C0 & C1' & TG & TI & CI & TC). pose proof (qs_chunk A it i ch rho QS) as (_ & _ & MS & IH & HT & HB & _).
  pose proof QS as [HG _ _ _ _ _ _ _ HSEP _ _ _ _]. destruct HSEP as (_ & HT' & _ & HC' & _).
  destruct HG as (_ & _ & TD & CD & _). destruct TD as (_ & _ & _ & _ & _ & TB). destruct CD as (_ & _ & _ & _ & CB).
  intros z z' Hz Hz' NE. unfold ZULh in Hz, Hz'. cbn [In] in Hz, Hz'. unfold zbLh, zbX, zloS, zhiX, IMG_HI, kPtrArrayReserve, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
  repeat (destruct Hz as [<-|Hz]); try (exfalso; exact Hz); repeat (destruct Hz' as [<-|Hz']); try (exfalso; exact Hz'); try (exfalso; apply NE; reflexivity);
    unfold NC, ms, h, PAB, CTX, T, G in *; clear -C1 C2 P1 P2 P3 P4 P5 P6 P7 T0 T1 C0 C1' TG TI CI TC MS IH HT HB HT' HC' TB CB; lia.
Qed.
End EnvH.

Lemma sF_parts : ltac2:(tb__ "0|6|
S13S86S69R2R1A2S1S0S13S17S5aS88R2A1A2U8M0A3S1S0S14Sa8S67R3S82R2A1M1S83R2A1A3A1S16A3S1S0S14S6eR3S5eS26S59S98G1U0A2A1A1A3S16A3S1S0S14S42S24S24S43S24S2dR1A1M2S2aS59S82R3A1A1A1A3Lg;S62R3A1M3A3S16A3S1S0S14S42S24S2cSb1A1G3A3S16A3S1S13S40S13R1S15S13U1M4S15S13U3S15S13U5S15S13U7S1bS13A1A3A3A3A3A3S1S0S14Sa8S68R5S5dR4R2A2M5S83R4A1R2A4A1S16A3S1S0S14S6eR5S5eS26S59S98G5G4A2A1A1A3S16A3S0S14S61S26S59G5A1A1S7cS7aS79A2A2S16A3A2A2F_;Fk;S13S47R1G0A2S0S14S42S24S24S43S24G2S2aS59S5dR5R3A2A1A1A3LF;S60R2A1A3S16A3F_;Fk;A2A2A2A2A2A2F_;Fcf;FnW;").
Proof.
  intros nW cf [H]. unfold scanF_chk in H. repeat (apply andb_prop in H as [H ?]).
  split; [apply Nat.eqb_eq; exact H|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split.
  - intros k Hk. match goal with X : forallb _ [1; 3; 5; 7]%nat = true |- _ => pose proof (proj1 (forallb_forall _ _) X k Hk) as Y end.
    cbv beta in Y. apply andb_prop in Y as [Y Y3]. apply andb_prop in Y as [Y1 Y2]. split; [exact Y1 | split; [exact Y2 | exact Y3]].
  - intros k Hk. match goal with X : forallb _ (seq 0 8) = true |- _ => apply (proj1 (forallb_forall _ _) X k) end. apply in_seq. lia.
Qed.
Lemma sV_parts : ltac2:(tb__ "0|3|
S13S86S13S14S87S5fR5R4R3R2R1A5S13S40S13R1S15S13U0S15S13U2S15S13U4S15S13U6S1bS13A1A3A3A3A3A3S1S0S1aS5bA1S9dS5dR7R2A2M0S15S9bS9cS7eG0S15S22Sa0S1bS22A1A3A2A1S1bS9bA1A3A2S19S5bS65G0A1M1A2A3S1S0S14S61S26S59G1A1A1Sa0A2S16A3S1S0S14S61S26S59S64G0A1M2A1A1S7cS7aS79A2A2S16A3S1S0S14Sa9S66R8G0S85R4A1R6R2R5A6S50S52R2A1A1S51A3S16A3S0S14S6eR8S4cR5A1S26S59S98G2U1A2A1A1A3S16A3A2A2A2A2F_;Fk;F_;Fcv;Fl;Ff;Fcf;FnW;").
Proof.
  intros nW cf f l cv [H] k Hk. unfold scanV_chk in H. pose proof (proj1 (forallb_forall _ _) H k Hk) as X. cbv beta zeta in X.
  apply andb_prop in X as [X X5]. apply andb_prop in X as [X X4]. apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2].
  split; [|split; [exact X2 | split; [exact X3 | split; [exact X4 | exact X5]]]].
  unfold selb in X1. unfold Lx_hb, selX. destruct (apply_axforms (lfh cf k) [AXSelect (sel_last (lfh cf k) [O_sh])]); [reflexivity | discriminate X1].
Qed.
Lemma leaf_k : ltac2:(tb__ "0|1|
S86S5aS0S13S17S5aS88R2A1A2U8M0A3S40S5aR2S88R3A1A3S4S13S13S1S47R1G0A2S0S5bS5cR4A1S5dR5R1A2A3A2Lk;A2F_;F_;FLf;Fcf;").
Proof.
  intros cf Lf HL HIN. destruct (In_nth _ _ Lf HIN) as (k & Hk & Ek). exists k. split; [lia|]. unfold lfh.
  rewrite (nth_indep _ (hf_SC cf) (la_state Lf)) by (rewrite length_map; exact Hk). rewrite map_nth, Ek. reflexivity.
Qed.

Definition PIN0 (A : AA) (r : valuation) : Prop := ltac2:(tb__ "0|3|
S1S0S37Q40M0A1M1S21Vr;Pc8A2S36G0SdSaVA;A1M2A1A2A3S1S0G1S21Vr;Pc9A2S36G0S30S17S6S7VA;A1A2A1A2A3S0G1S21Vr;Pc3A2S36G0S2fSbG2A1S75A2A2A3A2A2").
Lemma PIN0_eq : ltac2:(tb__ "0|0|
S10S20S20S3aR3R2A2S39S40S39R1S89A3S0S37Q40A1S21R4R2A2S21R5R2A2A3F_;Fv;S3aR5R3A2F_;F_;Fr';Fr;FA;").
Proof. intros A r r' (E1 & E2 & E3) H. unfold PIN0. rewrite !H by (unfold VS0h; cbn; tauto). split; [exact E1 | split; [exact E2 | exact E3]]. Qed.

Definition chsep (A : AA) (j : nat) (chj : sec_chunk) : Prop := ltac2:(tb__ "0|8|
SaVA;A1S11S1S2S2eS2fS8Vchj;A1M0S9Vchj;A1A2M1SbR1A1M2A2S2eS2fS2fG2S75A2Z1000M3A2G0A2A2S1S2S2eG1SeR1A1M4A2S2eS2fG4G3A2G0A2A2S1S2S2eG1SdR1A1M5A2S2eS2fG5S71A2G0A2A2S1S2S2eG1ScR1A1M6A2S2eS2fG6G3A2G0A2A2S13S6S0S1aS6A1S3fS6S7VA;A1R2A3S19S6R1A2A3S5S0S13Vj;R3A3A1S2S2eG1S8R3A1M7A2S2eS2fG7S9R3A1A2G0A2A2F_;F_;Fch';Fj';A2A2A2A2TG;").

Lemma Forall2_in_zone_W : ltac2:(tb__ "0|1|
S20S13S38F_;M0G0G0S18S13A1S18S22A1S18S57A1S41S22S57S58R7R6R5R4R3A5R2R1A5S41S22S57S6dR8R7R6R5R4A5R3R2A5F_;Fds;Fobjs;FZU;Fzhi;Fzlo;Fzb;Frho;").
Proof. intros rho zb zlo zhi ZU objs ds H. induction H; constructor; [apply in_zone_W; assumption | assumption]. Qed.

Section ExitH.
Variables (A : AA) (it : Z * Z) (i : nat) (ch : sec_chunk).
Let PAB : Z := ag_pab (aa_geom A).
Let NC : Z := Z.of_nat (length (aa_sec A)).
Let G : ageom := aa_geom A.
Let h : Z := sc_map_beg ch.
Let msz : Z := sc_map_size ch.

Lemma tbl_cell_h: ltac2:(tb__ "0|2|
S20S13S6S46VA;Vit;Vi;Vch;R3A5S0S1aS6A1S3fS6S7VA;A1R3A3S19S6R2A2A3S1Sa4Sa6S3dS29R5A1A2Sa5S2fVPAB;S31Z8S30R4A1M0A2A2U8S8R3A1M1A3A2S1S32G0VNC;A2S1S32Z0G1A2S32G1S33Z2Z2fA2A2A2A2A2F_;F_;Fchj;Fj;Fr;").
Proof.
  intros r j chj QS Hj. pose proof QS as [HG _ _ _ HSR _ _ _ _ _ _ _ _]. destruct HSR as (SC1 & _).
  destruct (SC1 j chj Hj) as (_ & _ & _ & _ & CP & _ & _ & _ & _ & D10 & _ & D12 & _).
  pose proof (proj1 (nth_error_Some (aa_sec A) j) ltac:(rewrite Hj; discriminate)) as LT.
  pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG).
  destruct D10 as (E1 & E2 & _). split; [exact CP|]. unfold NC. split; [lia|]. clear -E1 E2 D12 TG. lia.
Qed.

Lemma cell_carve_h : ltac2:(tb__ "0|6|
S20S25S25S13S6S46VA;Vit;Vi;Vch;R5A5S0S1aS6A1S3fS6S7VA;A1R3A3S19S6R2A2A3S0S37Q40M0A1M1S23R7R6A2S36G0S2fVPAB;S31Z8M2S30R4A1A2A2A2A3S0G1S23R8R6A2S36G0S8R4A1A2A3S1S6aS94Sa7R9A1S55R8R7A2M3A3S41S22S57S6dR9S3cVA;Vch;S2fVPAB;S31G2S30R6A1A2A2A3S49S4bS9Vch;A1A1S5eA5S6bS94S22S95G3A4S15S1dS1dS13S38A2M4S38A2M5S1cG4S38S1cS13S38U9Z0A4G2A4S1bG5A1A3A5A2F_;F_;F_;F_;Fchj;Fj;Fv;Fb;Fr4;").
Proof.
  intros r4 b v j chj QS Hj Eb Ev.
  destruct (tbl_cell_h r4 j chj QS Hj) as (CP & LT & MB). pose proof (tbl_nums_h A it i ch r4 QS) as (P1 & P2 & P3 & _).
  fold PAB in P1, P2. fold NC in P3. unfold IMG_HI, kPtrArrayReserve in *.
  pose proof (geom_nums _ (hb_hg _ _ _ _ _ QS)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG).
  assert (R : 0x646000 <= PAB + 8 * Z.of_nat j /\ PAB + 8 * Z.of_nat j + 8 <= 2 ^ 47) by (clear -P1 P2 P3 LT TG; lia).
  split.
  - unfold NSC. apply Forall_cons; [|apply Forall_nil]. unfold carve_okq. lazy beta iota zeta. rewrite Eb, u64_lit by (clear -R; lia).
    split; [lia|]. split; [lia|]. split; [lia|]. split; [clear -R; lia|]. split; [clear -R; lia|].
    split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|]. split.
    + intros off Hoff. apply (cell_wok_rd (rm r4) (PAB + 8 * Z.of_nat j) 8 (sc_map_beg chj) (PAB + 8 * Z.of_nat j + off) CP); [cbn [Z.of_nat]; lia | clear -R; lia | cbn [Z.of_nat]; clear -R; lia].
    + unfold cells_in_view. apply Forall_cons; [|apply Forall_nil]. intros jj Hjj.
      apply (civ_cell r4 (rm r4) (PAB + 8 * Z.of_nat j) 0 8 (sc_map_beg chj) v); [rewrite Z.add_0_r; exact CP | exact Ev | clear -R; lia | cbn [Z.of_nat]; clear -R; lia | exact Hjj].
  - unfold NSC. cbn [map carve_obj]. apply Forall2_cons; [|apply Forall2_nil]. apply in_zone_W. unfold in_zone. split; [unfold ZULh; cbn; tauto|]. split; [cbn; lia|]. split; [cbn; lia|]. right.
    unfold carved. rewrite obj_range_mk by lia. cbn [fst snd]. rewrite Eb, u64_lit by (clear -R; lia). unfold zbLh, zbX. lia.
Qed.

Lemma lst_facts_h : ltac2:(tb__ "0|9|
S20S6S46VA;Vit;Vi;Vch;R2A5S3bVA;S44S17S6S7VA;A1M0A2U1A2M1R2A3S0S1aS6A1S3fS6G0G1A3S19S6R3A2A3S1S2eS72S8R4A1M2A2S1S2eS2fG2S9R4A1M3A2M4SfVG;A1A2S1S2eZ12000G3A2S1S2S2eG4S74A2S2eS73G2A2A2S1S2S2eG4SeVG;A1M5A2S2eS2fG5Z1000M6A2G2A2A2S1S2S2eG4ScVG;A1M7A2S2eS2fG7G6A2G2A2A2S1S2S2eG4VPAB;A2S2eS2fVPAB;S71A2G2A2A2S1S5S0S13Vi;G1A3A1S2S2eS2fVh;Vmsz;A2S8R5A1M8A2S2eS2fG8S9R5A1A2Vh;A2A2F_;Sa4Sa6S3dS29R5A1A2Sa5S2fG2Z18A2U8S30G1A1A3A2A2A2A2A2A2A2A2A2F_;F_;F_;Flst;Fr;").
Proof.
  intros r lst QS SEP Hl. unfold chsep in SEP. cbv zeta in SEP. destruct SEP as (_ & S2 & S3 & S4 & _).
  pose proof QS as [_ _ _ _ HSR HI _ _ HSEP _ _ _ _]. destruct HSR as (SC1 & _).
  destruct (SC1 _ lst Hl) as (_ & _ & _ & C24 & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
  pose proof (dyn_in_big _ _ _ D10 ltac:(unfold PG in *; clear -D8 D9; lia)) as BIG. destruct D10 as (_ & _ & _ & _ & DB).
  assert (MS : 73728 <= sc_map_size lst).
  { rewrite D11. unfold round_up, PG in *. pose proof (Z.div_mod (sc_size lst + (4096 - 1)) 4096 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (sc_size lst + (4096 - 1)) 4096 ltac:(lia)). clear -D9 DM H. nia. }
  destruct HSEP as (_ & _ & _ & _ & HJ).
  split; [exact BIG|]. split; [exact D12|]. split; [exact MS|]. split; [exact DB|]. split; [exact S2|]. split; [exact S4|]. split; [exact S3|]. split; [|exact C24].
  intros NE. exact (HJ _ lst Hl NE).
Qed.

Lemma zsepE_h : ltac2:(tb__ "0|4|
S20S14S6S46VA;Vit;Vi;Vch;R3A5S3bVA;S44S17S6S7VA;A1M0A2U1A2M1R2A3S0S1aS6A1S3fS6G0G1A3S19S6R3A2A3S0S14R5S1eA3S47Vi;G1A2F_;S13S13S40S13R2S4cR8A1A3S40S13R2S4cR9A1A3S5S0S13R4R3A3A1S2S2eS2fS4dVA;Vi;Vch;RaR5A5M2S4bVmsz;R5A2A2S2fS4dVA;Vi;Vch;RaR4A5M3S49R4A1A2A2S2eS2fG3S4bVmsz;R4A2A2S2fG2S49R5A1A2A2A2F_;F_;F_;Fz';Fz;F_;F_;F_;F_;Flst;Fl;Fr;").
Proof.
  intros r l lst QS SEP Hl HLT. destruct (lst_facts_h r lst QS SEP Hl) as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & _).
  pose proof (tbl_nums_h A it i ch r QS) as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  pose proof (qs_nums A it i ch r QS) as (T0 & T1 & C0 & C1' & TG & TI & CI & TC). pose proof (qs_chunk A it i ch r QS) as (_ & _ & MS & IH & HT & HB & _).
  pose proof (geom_bands _ (hb_hg _ _ _ _ _ QS)) as (_ & TB & CB & _).
  pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite (hb_hi _ _ _ _ _ QS); discriminate)) as LTi.
  pose proof QS as [_ _ _ _ _ _ _ _ HSEP _ _ _ _]. destruct HSEP as (_ & HT' & _ & HC' & _).
  assert (Zi : 0 <= Z.of_nat i < NC) by (unfold NC; clear -LTi; lia).
  assert (Zl : l = false -> Z.of_nat i < NC - 1) by (intros E; specialize (HLT E); unfold NC; clear -HLT; lia).
  assert (L8' : l = false -> h + msz <= sc_map_beg lst \/ sc_map_beg lst + sc_map_size lst <= h) by (intros E; specialize (HLT E); apply L8; clear -HLT; lia).
  clear L8 HLT LTi.
  intros z z' Hz Hz' NE. unfold zbE, zbX, zloS, zhiX, IMG_HI, kPtrArrayReserve, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
  destruct l; unfold ZUXl in Hz, Hz'; cbn [In] in Hz, Hz'; [clear Zl L8' | specialize (Zl eq_refl); specialize (L8' eq_refl)];
    (repeat (destruct Hz as [<-|Hz]); try (exfalso; exact Hz); repeat (destruct Hz' as [<-|Hz']); try (exfalso; exact Hz'); try (exfalso; apply NE; reflexivity);
     unfold msz, h, G in *;
     first [ solve [clear -T0 T1 C0 C1' TG TI CI TC; lia]
           | solve [clear -TG TB CB T0 C0; lia]
           | solve [clear -MS IH HT HT' HC' HB TG; lia]
           | solve [clear -P1 P2 P3 P4 P5 P6 P7 Zi TG MS; lia]
           | solve [clear -P1 P2 P3 P4 P5 P6 P7 Zi Zl TG MS; lia]
           | solve [clear -L1 L2 L3 L4 L5 L6 L7 P3 Zi TG MS; lia]
           | solve [clear -L1 L2 L3 L4 L5 L6 L7 L8' P3 Zi Zl TG MS; lia] ]).
Qed.

Lemma exit_zones_hb : ltac2:(tb__ "0|5|
S20S20S14S6S25S46VA;Vit;Vi;Vch;R5A5S3bVA;S44S17S6S7VA;A1M0A2U1A2M1R3A3S0S1aS6A1S3fS6G0G1A3S19S6R4A2A3S3aVA;R7A2S4fVA;Vi;Vch;R7R6R8R5A7S1S6dR9S4dVA;Vi;Vch;R7A4M2S49S4bVmsz;A1M3S4cR8A1M4SabS50R6A1A1S51A7S41S22S57S6dR9G2S49G3G4A5S6bS94S22S95S53R8R6A2A4S54R8A1A5A2F_;F_;F_;F_;F_;FhT;Flst;Fl;Fr4;Fr0;").
Proof.
  intros r0 r4 l lst hT QS SEP Hl PN4 (EH & E203 & XT & XF).
  destruct (lst_facts_h r0 lst QS SEP Hl) as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & LC24).
  pose proof (tbl_nums_h A it i ch r0 QS) as (P1 & P2 & P3 & P4 & _). fold PAB in P1, P2, P4. fold NC in P3. unfold IMG_HI, kPtrArrayReserve in P1, P2, P3, P4.
  pose proof (qs_chunk A it i ch r0 QS) as (HP & MP & MS & IH & HTG & HBD & _ & _ & C0 & C8 & C24 & CPi & PSH). fold h msz in HP, MP, MS, IH, HTG, HBD, C0, C8, C24, PSH.
  pose proof (geom_nums _ (hb_hg _ _ _ _ _ QS)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG).
  pose proof PN4 as (E200 & E201 & _).
  pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite (hb_hi _ _ _ _ _ QS); discriminate)) as LTi.
  assert (EM : eval r4 vMS = Z_to_bv 64 msz) by (unfold vMS; cbn [eval]; exact E203).
  assert (EPb : eval r4 vPAB = Z_to_bv 64 PAB) by (unfold vPAB; cbn [eval]; exact E200).
  assert (ENc : eval r4 vNCH = Z_to_bv 64 NC) by (unfold vNCH; cbn [eval]; exact E201).
  assert (NCb : 1 <= NC /\ 8 * NC <= 2 ^ 23) by (unfold NC; clear -LTi P3; fold NC in P3; lia).
  assert (M8 : h mod 8 = 0 /\ msz mod 8 = 0).
  { unfold PG in HP, MP. destruct (proj1 (Z.mod_divide h 4096 ltac:(clear; lia)) HP) as [k1 E1]. destruct (proj1 (Z.mod_divide msz 4096 ltac:(clear; lia)) MP) as [k2 E2].
    rewrite E1, E2. replace (k1 * 4096) with (k1 * 512 * 8) by (clear; lia). replace (k2 * 4096) with (k2 * 512 * 8) by (clear; lia). split; apply Z_mod_mult. }
  assert (ELast : eval r4 (add (SAlu ALU_SLL vNCH (SLit 3)) vPAB) = Z_to_bv 64 (8 * NC + PAB)).
  { apply (eval_add_z r4 _ vPAB (8 * NC) PAB (eval_sll3 r4 vNCH NC ENc ltac:(clear -NCb; lia)) EPb); clear -NCb P1 P2 TG; lia. }
  unfold G in L2, L5, L6. unfold IMG_HI, PG, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
  assert (HR : 0x646000 <= h /\ h + msz < 2 ^ 47) by (clear -IH HTG TG; lia).
  split.
  - apply in_zone_W.
    unfold UX, uobj, ZDU, in_zone. split; [destruct l; unfold ZUXl; cbn [In]; clear; tauto|]. split; [cbn; clear; lia|]. split; [cbn; clear; lia|]. right.
    unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd]. rewrite soff_lit_small by (clear; lia).
    rewrite (soff_LENS r4 vMS msz EM ltac:(clear -MS HR; lia)), (eval_BSHS r4 hT h EH ltac:(clear -HR MS; lia)).
    pose proof (Sh_in_band h ltac:(clear -HR MS; lia)) as B1. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
    pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep.Sh_lt_HSE (h + msz) ltac:(clear -HR IH MS; lia)) as B2. unfold HIGH_SHADOW_END in B2. rewrite (Sh_add8 h msz (proj1 M8) (proj2 M8)) in B2.
    rewrite u64_lit by (clear -B1; lia). unfold zbE, zbX, LOW_SHADOW_BEG. clear -B1 B2. lia.
  - apply Forall2_in_zone_W.
    unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SegQS_loop.NX, ZDNX. cbn [map carve_obj app]. destruct l; cbn [map carve_obj app].
    + specialize (XT eq_refl). assert (Ei : Z.of_nat i = NC - 1) by (unfold NC; clear -XT LTi; lia).
      repeat apply Forall2_cons; try apply Forall2_nil; unfold in_zone; (split; [unfold ZUXl; cbn [In]; clear; tauto|]); (split; [cbn; clear -MS; lia|]); (split; [cbn; fold msz; clear -MS; lia|]); right;
        unfold carved; rewrite obj_range_mk by (clear; lia); cbn [fst snd]; rewrite ?EH, ?ELast, ?u64_lit by (clear -HR MS NCb P1 P2 TG; lia); unfold zbE, zbX; clear -Ei; lia.
    + destruct (XF eq_refl) as (XLT & E204 & E205 & E206). assert (Ei : Z.of_nat i < NC - 1) by (unfold NC; clear -XLT; lia).
      assert (EIdx : eval r4 (add vPAB (SAlu ALU_SLL vIDX (SLit 3))) = Z_to_bv 64 (PAB + 8 * Z.of_nat i)).
      { apply (eval_add_z r4 vPAB _ PAB (8 * Z.of_nat i) EPb (eval_sll3 r4 vIDX (Z.of_nat i) ltac:(unfold vIDX; cbn [eval]; exact E204) ltac:(clear -NCb Ei; lia))); clear -NCb P1 P2 TG Ei; lia. }
      assert (ELa : eval r4 vLAST = Z_to_bv 64 (sc_map_beg lst)) by (unfold vLAST; cbn [eval]; exact E205).
      repeat apply Forall2_cons; try apply Forall2_nil; unfold in_zone; (split; [unfold ZUXl; cbn [In]; clear; tauto|]); (split; [cbn; clear -MS; lia|]); (split; [cbn; fold msz; clear -MS; lia|]); right;
        unfold carved; rewrite obj_range_mk by (clear; lia); cbn [fst snd]; rewrite ?EH, ?ELast, ?EIdx, ?ELa, ?u64_lit by (clear -HR MS NCb P1 P2 TG Ei L1 L2 L3; lia); unfold zbE, zbX; clear; lia.
Qed.

Lemma exit_carve_h : ltac2:(tb__ "0|2|
S20S14S6S25S46VA;Vit;Vi;Vch;R4A5S3bVA;S44S17S6S7VA;A1M0A2U1A2M1R3A3S0S1aS6A1S3fS6G0G1A3S19S6R4A2A3S4fVA;Vi;Vch;R6R5R7R4A7S1SaaR8S50R5A1A2S6aS94Sa7R8A1S53R7R5A2A3A2F_;F_;F_;F_;FhT;Flst;Fl;Fr4;").
Proof.
  intros r4 l lst hT QS SEP Hl (EH & E203 & XT & XF).
  destruct (lst_facts_h r4 lst QS SEP Hl) as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & LC24).
  pose proof (tbl_nums_h A it i ch r4 QS) as (P1 & P2 & P3 & P4 & _). fold PAB in P1, P2, P4. fold NC in P3. unfold IMG_HI, kPtrArrayReserve in P1, P2, P3, P4.
  pose proof (qs_chunk A it i ch r4 QS) as (HP & MP & MS & IH & HTG & HBD & _ & _ & C0 & C8 & C24 & CPi & PSH). fold h msz in HP, MP, MS, IH, HTG, HBD, C0, C8, C24, PSH.
  pose proof (geom_nums _ (hb_hg _ _ _ _ _ QS)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG).
  pose proof (hb_hv _ _ _ _ _ QS) as (_ & E200 & E201 & _).
  pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite (hb_hi _ _ _ _ _ QS); discriminate)) as LTi.
  destruct (tbl_cell_h r4 _ lst QS Hl) as (CPl & _ & _).
  assert (EM : eval r4 vMS = Z_to_bv 64 msz) by (unfold vMS; cbn [eval]; exact E203).
  assert (EPb : eval r4 vPAB = Z_to_bv 64 PAB) by (unfold vPAB; cbn [eval]; exact E200).
  assert (ENc : eval r4 vNCH = Z_to_bv 64 NC) by (unfold vNCH; cbn [eval]; exact E201).
  assert (NCb : 1 <= NC /\ 8 * NC <= 2 ^ 23) by (unfold NC; clear -LTi P3; fold NC in P3; lia).
  assert (M8 : h mod 8 = 0 /\ msz mod 8 = 0).
  { unfold PG in HP, MP. destruct (proj1 (Z.mod_divide h 4096 ltac:(clear; lia)) HP) as [k1 E1]. destruct (proj1 (Z.mod_divide msz 4096 ltac:(clear; lia)) MP) as [k2 E2].
    rewrite E1, E2. replace (k1 * 4096) with (k1 * 512 * 8) by (clear; lia). replace (k2 * 4096) with (k2 * 512 * 8) by (clear; lia). split; apply Z_mod_mult. }
  assert (ELast : eval r4 (add (SAlu ALU_SLL vNCH (SLit 3)) vPAB) = Z_to_bv 64 (8 * NC + PAB)).
  { apply (eval_add_z r4 _ vPAB (8 * NC) PAB (eval_sll3 r4 vNCH NC ENc ltac:(clear -NCb; lia)) EPb); clear -NCb P1 P2 TG; lia. }
  unfold G in L2, L5, L6. unfold IMG_HI, PG, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
  assert (HR : 0x646000 <= h /\ h + msz < 2 ^ 47) by (clear -IH HTG TG; lia).
  split.
  -
    unfold UX, unk_ok. rewrite soff_lit_small by (clear; lia). rewrite (soff_LENS r4 vMS msz EM ltac:(clear -MS HR; lia)), (eval_BSHS r4 hT h EH ltac:(clear -HR MS; lia)).
    pose proof (Sh_in_band h ltac:(clear -HR MS; lia)) as B1. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
    pose proof (Z.div_pos msz 8 ltac:(clear -MS; lia) ltac:(clear; lia)). pose proof (Z.div_lt_upper_bound msz 8 (2 ^ 44) ltac:(clear; lia) ltac:(clear -HR IH MS; lia)).
    rewrite u64_lit by (clear -B1; lia).
    split; [clear -H; lia|]. split; [clear -H H0; lia|]. split; [clear -B1; lia|]. split; [clear -B1 H0; lia|].
    intros x Hx. rewrite <- (Sh_add8 h msz (proj1 M8) (proj2 M8)) in Hx. pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep.Sh_lt_HSE (h + msz) ltac:(clear -HR IH MS; lia)) as B2. unfold HIGH_SHADOW_END in B2.
    apply (wr_present (rm r4) (Sh h) (Sh (h + msz)) x PSH); [clear -Hx; lia | clear -B1; lia | clear -B2; lia | right; clear -B1; lia].
  -
    unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SegQS_loop.NX. apply Forall_app. split.
    + apply Forall_cons; [|apply Forall_nil].
      apply (carve1_ok A it ch r4 hT 0 16 _ h EH ltac:(clear -HR MS; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear -HR MS; lia)).
      * unfold cells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn; clear; lia.
      * intros z Hz. destruct (Z_lt_dec z (h + 8)) as [l0|n]; [exists 0, 8%nat, h; split; [cbn [Z.of_nat]; clear -Hz HR MS l0; lia | rewrite Z.add_0_r; exact C0] | exists 8, 8%nat, msz; split; [cbn [Z.of_nat]; clear -Hz HR MS n; lia | exact C8]].
      * repeat apply Forall_cons; try apply Forall_nil; [exists h; rewrite Z.add_0_r; split; [exact EH | exact C0] | exists msz; split; [exact EM | exact C8]].
    + destruct l.
      * specialize (XT eq_refl). assert (Ei : Z.of_nat i = NC - 1) by (unfold NC; clear -XT LTi; lia).
        assert (Elst : lst = ch) by (rewrite <- XT in Hl; rewrite (hb_hi _ _ _ _ _ QS) in Hl; injection Hl as <-; reflexivity).
        repeat apply Forall_cons; try apply Forall_nil.
        -- apply (carve1_ok A it ch r4 hT 24 32 _ h EH ltac:(clear -HR MS; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear -HR MS; lia)).
           ++ unfold cells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn; clear; lia.
           ++ intros z Hz. exists 24, 8%nat, (Z.of_nat i). split; [cbn [Z.of_nat]; clear -Hz HR MS; lia | exact C24].
           ++ repeat apply Forall_cons; try apply Forall_nil. exists (Z.of_nat i). split; [|exact C24]. rewrite Ei. apply ev_add_lit; [exact ENc | clear -NCb; lia | lia | clear -NCb; lia].
        -- apply (carve1_ok A it ch r4 _ (-8) 0 _ (8 * NC + PAB) ELast ltac:(clear -NCb P1 P2 TG; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear -NCb P1; lia)).
           ++ unfold cells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn; clear; lia.
           ++ intros z Hz. exists (-8), 8%nat, h. split; [cbn [Z.of_nat]; clear -Hz NCb P1 P2 TG; lia|]. replace (8 * NC + PAB + -8) with (PAB + 8 * Z.of_nat i) by (clear -Ei; lia). exact CPi.
           ++ repeat apply Forall_cons; try apply Forall_nil. exists h. split; [exact EH|]. replace (8 * NC + PAB + -8) with (PAB + 8 * Z.of_nat i) by (clear -Ei; lia). exact CPi.
      * destruct (XF eq_refl) as (XLT & E204 & E205 & E206). assert (Ei : Z.of_nat i < NC - 1) by (unfold NC; clear -XLT; lia).
        assert (ELn : Z.of_nat (length (aa_sec A) - 1) = NC - 1) by (unfold NC; clear -LTi; lia). rewrite ELn in LC24, CPl.
        assert (EIdx : eval r4 (add vPAB (SAlu ALU_SLL vIDX (SLit 3))) = Z_to_bv 64 (PAB + 8 * Z.of_nat i)).
        { apply (eval_add_z r4 vPAB _ PAB (8 * Z.of_nat i) EPb (eval_sll3 r4 vIDX (Z.of_nat i) ltac:(unfold vIDX; cbn [eval]; exact E204) ltac:(clear -NCb Ei; lia))); clear -NCb P1 P2 TG Ei; lia. }
        assert (ELa : eval r4 vLAST = Z_to_bv 64 (sc_map_beg lst)) by (unfold vLAST; cbn [eval]; exact E205).
        repeat apply Forall_cons; try apply Forall_nil.
        -- apply (carve1_ok A it ch r4 hT 24 32 _ h EH ltac:(clear -HR MS; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear -HR MS; lia)).
           ++ unfold cells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn; clear; lia.
           ++ intros z Hz. exists 24, 8%nat, (Z.of_nat i). split; [cbn [Z.of_nat]; clear -Hz HR MS; lia | exact C24].
           ++ repeat apply Forall_cons; try apply Forall_nil. exists (Z.of_nat i). split; [unfold vIDX; cbn [eval]; exact E204 | exact C24].
        -- apply (carve1_ok A it ch r4 _ 0 8 _ (PAB + 8 * Z.of_nat i) EIdx ltac:(clear -NCb P1 P2 TG Ei; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear -P1; lia)).
           ++ unfold cells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn; clear; lia.
           ++ intros z Hz. exists 0, 8%nat, h. split; [cbn [Z.of_nat]; clear -Hz NCb P1 P2 TG Ei; lia | rewrite Z.add_0_r; exact CPi].
           ++ repeat apply Forall_cons; try apply Forall_nil. exists h. rewrite Z.add_0_r. split; [exact EH | exact CPi].
        -- apply (carve1_ok A it ch r4 _ (-8) 0 _ (8 * NC + PAB) ELast ltac:(clear -NCb P1 P2 TG; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear -NCb P1; lia)).
           ++ unfold cells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn; clear; lia.
           ++ intros z Hz. exists (-8), 8%nat, (sc_map_beg lst). split; [cbn [Z.of_nat]; clear -Hz NCb P1 P2 TG; lia|]. replace (8 * NC + PAB + -8) with (PAB + 8 * (NC - 1)) by (clear; lia). exact CPl.
           ++ repeat apply Forall_cons; try apply Forall_nil. exists (sc_map_beg lst). split; [exact ELa|]. replace (8 * NC + PAB + -8) with (PAB + 8 * (NC - 1)) by (clear; lia). exact CPl.
        -- apply (carve1_ok A it ch r4 vLAST 24 32 _ (sc_map_beg lst) ELa ltac:(clear -L1 L2 L3 TG; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear -L1; lia)).
           ++ unfold cells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn; clear; lia.
           ++ intros z Hz. exists 24, 8%nat, (NC - 1). split; [cbn [Z.of_nat]; clear -Hz L1 L2 L3 TG; lia | exact LC24].
           ++ repeat apply Forall_cons; try apply Forall_nil. exists (NC - 1). split; [unfold vLIDX; cbn [eval]; exact E206 | exact LC24].
Qed.

Lemma exit_facts_h : ltac2:(tb__ "0|0|
S20S13S14S6S39S48R4U2A2S46VA;Vit;Vi;Vch;R6A5S4aR6SbSaVA;A1A1Vh;Vmsz;A4S4fVA;Vi;Vch;R6R5R8S2bR4A1A7S6aS24S27R9A1S63R8R7R5A3A3F_;F_;F_;F_;Fhv;Flst;Fl;Ff;Fr4;").
Proof.
  intros r4 f l lst hv Hf QS HFAM (EH & E203 & XT & XF).
  pose proof (qs_chunk A it i ch r4 QS) as (HP & MP & MS & IH & HTG & _). fold h msz in HP, MP, MS, IH, HTG.
  pose proof (geom_nums _ (hb_hg _ _ _ _ _ QS)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _ & TG). rewrite kSpaceSize_val in S2.
  pose proof (hb_hv _ _ _ _ _ QS) as (E165 & _ & E201 & _). pose proof (hb_hrig _ _ _ _ _ QS) as (_ & _ & E155 & _). pose proof (hb_hu _ _ _ _ _ QS) as HU. fold h in HU.
  pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite (hb_hi _ _ _ _ _ QS); discriminate)) as LTi.
  pose proof (tbl_nums_h A it i ch r4 QS) as (_ & _ & P3 & _). fold NC in P3. unfold kPtrArrayReserve in P3.
  unfold IMG_HI, PG, HIGH_SHADOW_END, TOPMAX in *.
  assert (EM : eval r4 vMS = Z_to_bv 64 msz) by (unfold vMS; cbn [eval]; exact E203).
  assert (EI : eval r4 mT = Z_to_bv 64 (h + 6128)) by (rewrite (proj1 (proj2 (proj2 (hb_E A it i ch r4 QS)))), HU; f_equal; clear; lia).
  assert (ES : eval r4 vSB = Z_to_bv 64 (ag_spacebeg (aa_geom A))) by (unfold vSB; cbn [eval]; exact E155).
  assert (HR : 0x646000 <= h /\ h + msz <= 140737479966720 /\ 73728 <= msz) by (clear -IH HTG TG MS; lia).
  assert (EA1 : eval r4 (add (SVar hv) vMS) = Z_to_bv 64 (h + msz)) by (apply (eval_add_z r4 _ vMS h msz EH EM); clear -HR; lia).
  assert (EA2 : eval r4 (add vMS (SVar hv)) = Z_to_bv 64 (msz + h)) by (apply (eval_add_z r4 vMS _ msz h EM EH); clear -HR; lia).
  assert (EA3 : eval r4 (add (SVar hv) (SLit 4096)) = Z_to_bv 64 (h + 4096)) by (apply ev_add_lit; [exact EH | clear -HR; lia | clear; lia | clear -HR; lia]).
  assert (M8 : h mod 8 = 0 /\ msz mod 8 = 0).
  { destruct (proj1 (Z.mod_divide h 4096 ltac:(clear; lia)) HP) as [k1 E1]. destruct (proj1 (Z.mod_divide msz 4096 ltac:(clear; lia)) MP) as [k2 E2].
    rewrite E1, E2. replace (k1 * 4096) with (k1 * 512 * 8) by (clear; lia). replace (k2 * 4096) with (k2 * 512 * 8) by (clear; lia). split; apply Z_mod_mult. }
  unfold F2Xh. cbv zeta. apply Forall_app. split; [|apply Forall_app; split].
  - repeat apply Forall_cons; try apply Forall_nil.
    + apply (F_lenX_holds r4 (SVar hv) h msz EH EM); [clear -HR; lia | clear -HR; lia | clear -HR; lia | exact (proj1 M8) | exact (proj2 M8)].
    + apply (hne0 r4 _ h EH). clear -HR. lia.
    + apply (hle r4 _ mT h (h + 6128) EH EI); clear -HR; lia.
    + apply (hlt r4 mT _ (h + 6128) (h + msz) EI EA1); clear -HR; lia.
    + cbn [holds]. split; [clear; lia|]. cbn [eval] in EH. rewrite EH, u64_lit by (clear -HR; lia). change (2 ^ 12) with 4096. exact HP.
    + cbn [holds]. split; [clear; lia|]. rewrite E203, u64_lit by (clear -HR; lia). change (2 ^ 12) with 4096. exact MP.
    + apply (hle r4 _ vMS 73728 msz (elit r4 _) EM); clear -HR; lia.
    + apply (hle r4 vMS _ msz 140737479966720 EM (elit r4 _)); clear -HR; lia.
    + apply (hle r4 _ (SVar hv) 0x646000 h (elit r4 _) EH); clear -HR; lia.
    + apply (hle r4 _ _ (h + msz) 140737479966720 EA1 (elit r4 _)); clear -HR; lia.
    + apply (hle r4 _ _ (msz + h) 140737479966720 EA2 (elit r4 _)); clear -HR; lia.
  - unfold F_hX. destruct f as [|[|[|f]]]; [| | | exfalso; clear -Hf; lia]; cbn [fam_ok] in HFAM; repeat apply Forall_cons; try apply Forall_nil.
    + apply (hle r4 _ _ (h + msz) 0x7fff7000 EA1 (elit r4 _)); clear -HR HFAM; lia.
    + apply (hle r4 _ _ (msz + h) 0x7fff7000 EA2 (elit r4 _)); clear -HR HFAM; lia.
    + apply (hlt r4 _ vSB (h + 4096) (ag_spacebeg (aa_geom A)) EA3 ES); clear -HR HFAM S1 S2 TG; lia.
    + apply (hle r4 _ (SVar hv) 0x10007fff8000 h (elit r4 _) EH); clear -HR HFAM; lia.
    + apply (hlt r4 _ vSB (h + 4096) (ag_spacebeg (aa_geom A)) EA3 ES); clear -HR HFAM S1 S2 TG; lia.
    + apply (hle r4 _ (SVar hv) 0x10007fff8000 h (elit r4 _) EH); clear -HR HFAM S1 S2; lia.
    + apply (hle r4 (add vSB (SLit (2 ^ 37))) _ (ag_spacebeg (aa_geom A) + 2 ^ 37) (h + 4096)); [apply ev_add_lit; [exact ES | clear -S1 S2 TG; lia | clear; lia | clear -S1 S2 TG; lia] | exact EA3 | clear -S1 S2 TG; lia | clear -HR; lia | clear -HFAM; lia].
  - destruct l; [apply Forall_nil|]. destruct (XF eq_refl) as (XLT & E204 & _). apply Forall_cons; [|apply Forall_nil].
    apply (hlt r4 vIDX _ (Z.of_nat i) (NC - 1)); [unfold vIDX; cbn [eval]; exact E204 | apply ev_add_lit; [unfold vNCH; cbn [eval]; exact E201 | | clear; lia |] | | |]; unfold NC in *; clear -XLT LTi P3; lia.
Qed.
End ExitH.

Section LoopH.
Variables (nW : nat) (Kc : KcA).
Hypothesis HKc : Kc_ok Kc.
Hypothesis HUS : ltac2:(tb__ "0|0|
Sb4Sa2VnW;A1Sa1A2").
Variables (A : AA) (rho1 : valuation) (p n : Z) (i : nat) (ch : sec_chunk) (f : nat) (TZ : Z -> Prop).
Hypothesis HI : ltac2:(tb__ "0|0|
S0S1aS6A1S3fS6S7VA;A1Vi;A3S19S6Vch;A2A3").
Hypothesis HU : ltac2:(tb__ "0|0|
S0S38Vp;S2fS2fS8Vch;A1S77A2Z800A2A3").
Hypothesis HSZ : ltac2:(tb__ "0|0|
S0S38S12Vch;A1S2fS78Vn;Z8A2Z1000A2A3").
Hypothesis HN : 1 <= n.
Hypothesis HNB : ltac2:(tb__ "0|0|
S2eS2fZ1800S9fVn;A1A2S9Vch;A1A2").
Hypothesis Hf : (f <= 2)%nat.
Hypothesis HFAM : ltac2:(tb__ "0|0|
S4aVf;SbSaVA;A1A1S8Vch;A1S9Vch;A1A4").
Hypothesis HPIN : ltac2:(tb__ "0|4|
S1S0S37Q40M0A1M1S21Vrho1;P97A2S36G0SeSaVA;A1M2A1A2A3S1S0G1S21Vrho1;P98A2S36G0ScG2A1A2A3S1S0G1S21Vrho1;P9bA2S36G0SbG2A1A2A3S1S0G1S21Vrho1;PcA2S36G0Vp;A2A3S1S0G1S21Vrho1;P69A2S36G0S9fVn;A1M3A2A3S0G1S21Vrho1;P6aA2S36G0S34G3Z8A2A2A3A2A2A2A2A2").

Hypothesis HTZ_sh : ltac2:(tb__ "0|0|
S38S9aVch;R1A2VTZ;R2A1F_;Fz;").
Hypothesis HTZ_tbl : ltac2:(tb__ "0|1|
S38S1S2eSdSaVA;A1A1M0R1A2S32R1S2fG0S71A2A2A2VTZ;R2A1F_;Fz;").
Let it : Z * Z := ltac2:(tb__ "0|0|
S1cS38S38Vp;Vn;A4").
Let JH : jpredA := ltac2:(tb__ "0|0|
SacS3dS9aVch;A1VTZ;Sb0VnW;Sa1S1eVA;VKc;Vrho1;A6A4").
Let PAB : Z := ag_pab (aa_geom A).
Let NC : Z := Z.of_nat (length (aa_sec A)).
Let maps : list Z := map sc_map_beg (aa_sec A).
Let pp : Z := fst it - 16.
Variables (Elf : axst) (cf : hbfam).
Hypothesis FOK : ltac2:(tb__ "0|0|
S8bVElf;Vf;Vcf;A3").
Hypothesis SF : hbscanF_ok nW cf.
Definition FCH1 : Prop := ltac2:(tb__ "0|0|
S6aS24S27Vrho1;A1S62VnW;A1A3").

Lemma env_at : ltac2:(tb__ "0|1|
S20S18S37Q40A1M0A1S18S97A1S96VJH;R4R3R2R1A4S3aVA;R5A2S1S46VA;Vit;Vi;Vch;R6A5S1S39Sb6R1S3eA2S0G0S21R8R2A2S21Vrho1;R2A2A3F_;Fv;S1S39S0S18S37Q8A1A1S28R7R1A2S28Vrho1;R1A2A3Fl0;S1S4S20S20S1Sa3VA;R1A2SadS3dS9aVch;A1VTZ;R1R7A5A2Lrp;A2S13S6S0S1aS6A1S3fS6S7VA;A1R2A3S19S6R1A2A3S3bVA;R3R2A3F_;Fchj;Fj;A2A2A2A2F_;F_;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md HJ (E200 & E201 & E195).
  assert (RLL : forall l0, rl r l0 = rl rho1 l0).
  { destruct HJ as (rp & (Hag & _) & BR). destruct BR as (_ & BL & _). destruct Hag as (_ & Hl & _). intros l0. rewrite BL. symmetry. apply Hl. }
  destruct (JH_parts nW Kc A rho1 ch TZ r tp tr md HJ) as (rp & HA & HK & Htp & Htop & BR & RW4).
  destruct HPIN as (P151 & P152 & P155 & P12 & P105 & P106).
  assert (RP : forall v, (v < GW)%positive -> rw rp v = rw rho1 v) by (intros v Hv; rewrite <- (proj1 BR v); exact (RW4 v Hv)).
  assert (E151 : rw rp 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))) by (rewrite RP by (unfold GW; lia); exact P151).
  assert (E152 : rw rp 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))) by (rewrite RP by (unfold GW; lia); exact P152).
  assert (E155 : rw rp 155%positive = Z_to_bv 64 (ag_spacebeg (aa_geom A))) by (rewrite RP by (unfold GW; lia); exact P155).
  pose proof (hbenv_intro Kc HKc A p n i ch HI HU HSZ HN TZ rp r tp tr md HA HK Htp Htop E151 E152 E155 BR
                ltac:(rewrite RW4 by (unfold GW; lia); exact P12) E200 E201 E195) as QS.
  split; [exact QS|]. split; [exact RW4|]. split; [exact RLL|]. split; [exists rp; split; [exact Htop | exact BR]|].
  set (rpK := rho_sets rp [(156%positive, Z_to_bv 64 (ag_spacebeg (aa_geom A) + kSpaceSize))]).
  assert (ERM : rm rpK = rm rp) by (unfold rpK; apply rm_rho_sets).
  assert (OTH : forall v, v <> 156%positive -> rw rpK v = rw rp v) by (intros v Hv; unfold rpK; rewrite rho_sets_other; [reflexivity | cbn; intros [X|[]]; congruence]).
  assert (HK0 : K0 Kc A rpK tp tr md).
  { split; [|split; [exact HK|split; [|split]]].
    - pose proof (AInvA_Q A rp tp md HA) as HQ. unfold AInvQ in *. rewrite ERM. exact HQ.
    - unfold tp_ok in *. rewrite OTH by discriminate. exact Htp.
    - unfold top_high in *. unfold V_DEPTH in *. rewrite !OTH by discriminate. exact Htop.
    - unfold rigidQ. rewrite !OTH by discriminate. split; [exact E151|]. split; [exact E152|]. split; [exact E155|].
      unfold rpK. apply rho_sets_get; [cbn; repeat constructor; cbn; tauto | cbn; tauto]. }
  intros j chj Hj. exact (ks_sep segsA (K0 Kc) (K0_sec Kc HKc) A rpK tp tr md HK0 j chj Hj).
Qed.

Lemma zenv_at : ltac2:(tb__ "0|0|
S20S18S37Q40A1A1S18S97A1S96VJH;R4R3R2R1A4S3aVA;R5A2S8cS6fVnW;VA;Vp;Vn;Vch;R7A6F_;F_;F_;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md HJ P0 F1. destruct (env_at r tp tr md HJ P0) as (QS & RW4 & RLL & (rp & Htop & BR) & _).
  destruct (sF_parts nW cf SF) as (_ & _ & _ & _ & FCHB & _).
  assert (AV : agree_vals NPRE rho1 r) by (split; [intros v Hv; symmetry; apply RW4; exact Hv | intros l0; symmetry; apply RLL]).
  assert (F4 : forall g, In g (FCHs nW) -> holds r g).
  { intros g Hg. apply (proj1 (holds_agree_vals NPRE rho1 r g AV (proj1 (forallb_forall _ _) FCHB g Hg))). exact (proj1 (Forall_forall _ _) F1 g Hg). }
  apply (zenv_of nW A rho1 p n i ch TZ HU HN HNB HPIN rp r QS Htop BR RW4).
  - assert (D1 : holds r (SPBranch BC_GE (SLit (- free_depth)) (SVar V_DEPTH))) by (apply F4; unfold FCHs; apply in_or_app; right; left; reflexivity).
    cbn [holds eval branch_taken] in D1. unfold bv_lts in D1. apply negb_true_iff in D1. apply Z.ltb_ge in D1.
    change (bv_signed (Z_to_bv 64 (- free_depth))) with (- free_depth) in D1. exact D1.
  - apply Forall_forall. intros g Hg. apply F4. unfold FCHs. apply in_or_app. left. exact Hg.
Qed.
Lemma zs_L : ltac2:(tb__ "0|0|
S20S38S18S22A1S6fVnW;VA;Vp;Vn;Vch;R3A6S0S14S6eVnW;S5eR2A3S16A3S41S22S57S6dR5S3cVA;Vch;R4A3S49S4bS9Vch;A1A1S5eA5R3S70VnW;R3A2A5F_;F_;Fobjs;Fc9;Fr;").
Proof. intros r c9 objs ZE HB. apply (zds_sound nW A p n ch r (zbLh A ch c9) zloS (zhiX (sc_map_size ch)) ZULh); try (repeat split; reflexivity); [exact ZE | exact HB]. Qed.

Lemma first_glue_h : ltac2:(tb__ "0|0|
S20S18S37Q40A1A1S81S3aVA;R3A2S45S3dVJH;S82Vcf;A1R4R3R2A6S4S20S20S1S45S3dVJH;S83Vcf;A1R1R5R4A6S1S3aVA;R1A2S1S4eVA;Vit;U0R1A4S8cA2A2A2Lrho2;A2F_;F_;Fw;Ftp;Fr;").
Proof.
  intros r tp [tr [ms md]] P0 H.
  destruct (sF_parts nW cf SF) as (_ & TOK & ZOK & FCHA & FCHB & _).
  pose proof (JF_stable nW UStopLe false A Kc rho1 HUS HKc) as HST. change GW with NPRE in HST.
  destruct (env_at r tp tr md (proj2 H) P0) as (QS & RW0 & RL0 & _ & _).
  assert (F1 : FCH1).
  { pose proof (SPA_facts_hold segsA _ r (hf_LA cf) tp _ H) as HFa.
    assert (AV : agree_vals NPRE r rho1) by (split; [intros v Hv; apply RW0; exact Hv | intros l0; apply RL0]).
    apply Forall_forall. intros g Hg. apply (proj1 (holds_agree_vals NPRE r rho1 g AV (proj1 (forallb_forall _ _) FCHB g Hg))).
    pose proof (proj1 (forallb_forall _ _) FCHA g Hg) as X. apply existsb_exists in X as (g' & Hg' & Eg). apply sprop_eqb_sound in Eg. subst g'.
    exact (proj1 (Forall_forall _ _) HFa g Hg'). }
  destruct (nth_error (aa_sec A) 0) as [ch0|] eqn:E0.
  2:{ exfalso. apply nth_error_None in E0. pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite HI; discriminate)). lia. }
  destruct (tbl_cell_h A it i ch r 0%nat ch0 QS E0) as (CP0 & LT0 & MB0).
  pose proof P0 as (E200 & E201 & _).
  pose proof (tbl_nums_h A it i ch r QS) as (P1 & P2 & P3 & _). fold PAB in P1, P2. fold NC in P3. unfold IMG_HI, kPtrArrayReserve in P1, P2, P3.
  pose proof (geom_nums _ (hb_hg _ _ _ _ _ QS)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG).
  destruct (s_stepW (chunk_sh_zone ch) TZ (JF nW UStopLe false A Kc rho1) HST (zbLh A ch (PAB + 8 * Z.of_nat 0)) zloS (zhiX (sc_map_size ch)) ZULh
              (zsepLh A it i ch r (PAB + 8 * Z.of_nat 0) QS ltac:(cbn; lia) ltac:(fold PAB; unfold kPtrArrayReserve; cbn [Z.of_nat]; clear -P3 LT0; lia))
              (T_first_hb nW (hf_LA cf) (hf_SC cf)) [] [Z_to_bv 64 (sc_map_beg ch0)] r tp tr ms md TOK (keepN0 (hf_LA cf)) eq_refl H (Forall_nil _)) as (rho5 & H5 & V5 & RM5 & AG5 & EV).
  { intros EV3 HJ4. set (rho3 := rho_absorb r (map dobj []) (vms md tp ms)) in *.
    set (rho4 := rho_sets rho3 (combine (s_bs (T_first_hb nW (hf_LA cf) (hf_SC cf))) [Z_to_bv 64 (sc_map_beg ch0)])) in *.
    assert (P4 : PIN0 A rho4).
    { apply (PIN0_eq A r rho4 P0). intros v Hv. unfold rho4. rewrite rho_sets_other; [reflexivity|]. cbn. intros [<-|[]]. unfold VS0h in Hv. cbn in Hv. intuition discriminate. }
    destruct (env_at rho4 tp tr md HJ4 P4) as (QS4 & _). pose proof (zenv_at rho4 tp tr md HJ4 P4 F1) as ZE4.
    pose proof P4 as (E200' & _).
    assert (E211 : rw rho4 211%positive = Z_to_bv 64 (sc_map_beg ch0)) by (unfold rho4; apply rho_sets_get; [cbn; repeat constructor; cbn; tauto | cbn; tauto]).
    destruct (cell_carve_h A it i ch rho4 vPAB (SVar 211) 0%nat ch0 QS4 E0
                ltac:(unfold vPAB; cbn [eval Z.of_nat]; rewrite E200'; f_equal; fold PAB; lia) ltac:(cbn [eval]; exact E211)) as (C1 & C2).
    split; [exact C1|]. split; [exact C2|]. split; [exact (zs_L rho4 _ _ ZE4 ZOK)|]. intros _. apply Forall_nil. }
  exists rho5. split; [exact H5|].
  set (rho4 := rho_sets (rho_absorb r (map dobj []) (vms md tp ms)) (combine (s_bs (T_first_hb nW (hf_LA cf) (hf_SC cf))) [Z_to_bv 64 (sc_map_beg ch0)])) in *.
  assert (OT : forall v, v <> 211%positive -> rw rho4 v = rw r v) by (intros v Hv; unfold rho4; rewrite rho_sets_other; [reflexivity | cbn; intros [X|[]]; congruence]).
  assert (E211 : rw rho4 211%positive = Z_to_bv 64 (sc_map_beg ch0)) by (unfold rho4; apply rho_sets_get; [cbn; repeat constructor; cbn; tauto | cbn; tauto]).
  split; [|split; [|exact F1]].
  - apply (PIN0_eq A r rho5 P0). intros v Hv. rewrite (V5 v (SVar v)).
    + cbn [eval]. apply OT. unfold VS0h in Hv. cbn in Hv. intuition (subst; discriminate).
    + unfold T_first_hb, M_first_hb. cbn [s_M]. apply in_or_app. left. unfold idm. apply in_map_iff. exists v. split; [reflexivity | exact Hv].
  -
    unfold SCANI.
    rewrite (V5 210%positive vPAB ltac:(unfold T_first_hb, M_first_hb; cbn; tauto)), (V5 213%positive (add vPAB (SAlu ALU_SLL vNCH (SLit 3))) ltac:(unfold T_first_hb, M_first_hb; cbn; tauto)),
            (V5 212%positive (SLit 0) ltac:(unfold T_first_hb, M_first_hb; cbn; tauto)), (V5 211%positive (SVar 211) ltac:(unfold T_first_hb, M_first_hb; cbn; tauto)).
    assert (EP : eval rho4 vPAB = Z_to_bv 64 PAB) by (unfold vPAB; cbn [eval]; rewrite OT by discriminate; exact E200).
    assert (ENc : eval rho4 vNCH = Z_to_bv 64 NC) by (unfold vNCH; cbn [eval]; rewrite OT by discriminate; exact E201).
    split; [rewrite EP; f_equal; cbn [Z.of_nat]; lia|]. split; [|split; [reflexivity | cbn [eval]; rewrite E211, (maps_nth A 0 ch0 E0); reflexivity]].
    apply (eval_add_z rho4 vPAB _ PAB (8 * NC) EP (eval_sll3 rho4 vNCH NC ENc ltac:(clear -P3 LT0; lia))); [clear -P1; lia | clear -LT0; lia | clear -P1 P2 P3 TG; lia].
Qed.

Lemma leaf_facts_h : ltac2:(tb__ "0|0|
S13S20S18S37Q40A1A1S81S47R4U8A2S45S3dVJH;S5dVcf;R5A2R4R3R2A6S6aS24S27R5A1S60R6A1A3F_;F_;Fw;Ftp;Fr;Fk;").
Proof.
  intros k r tp w Hk H. pose proof (SPA_facts_hold segsA _ r (lfh cf k) tp w H) as HFa. apply Forall_forall. intros F HF.
  destruct (sF_parts nW cf SF) as (_ & _ & _ & _ & _ & _ & LFOK).
  pose proof (proj1 (forallb_forall _ _) (LFOK k Hk) F HF) as X. apply existsb_exists in X as (g & Hg & Eg). apply sprop_eqb_sound in Eg. subst g.
  exact (proj1 (Forall_forall _ _) HFa F Hg).
Qed.

Lemma leaf_vals_h : ltac2:(tb__ "0|7|
S13S13S20S20S18S37Q40M0A1M1A1S81S6S47R7U8A2S46VA;Vit;Vi;Vch;R5A5S4eVA;Vit;R8R7A4S0S1aS6A1S3fS6S7VA;A1M2R9A3S19S6R4A2A3S92S91S84A1R9R8A3S45S3dVJH;S5dVcf;RcA2R9R8R7A6S1S0G1S23RaS7aA2S36G0S2fVPAB;S31Z8M3S30RcA1A2A2A2A3S1S0G1S23RaS7fA2S36G0S2fVPAB;S31G3VNC;A2A2A2A3S1S0G1S23RaS79A2S36G0S8R7A1A2A3S1S0G1S23RaS52RdA1A2S36G0Sb2S6cS38S1fRcA1Vmaps;A3Vpp;A2A2A3S1S0S14Sb5RdA1M4S16A3S0S13S1fRdA1M5S17S6G2A2M6A3F_;S0S14G4S1eA3S47G5G6A2F_;A2A2A2A2A2F_;F_;F_;F_;F_;F_;Fchj;Fw;Ftp;Frho';Frho;Fj;Fk;").
Proof.
  intros k j rho rho' tp w chj Hk QS (E210 & E213 & E212 & E211) Hj HKp H.
  pose proof (leaf_facts_h k rho' tp w Hk H) as HLF.
  assert (KV : forall v, In v VSCh -> rw rho' v = rw rho v) by (intros v Hv; rewrite (proj2 HKp v (SVar v) ltac:(unfold idm; apply in_map_iff; exists v; split; [reflexivity | exact Hv])); reflexivity).
  destruct (tbl_cell_h A it i ch rho' j chj QS Hj) as (CP & LT & MB). pose proof (tbl_nums_h A it i ch rho' QS) as (P1 & P2 & P3 & _).
  fold PAB in P1, P2. fold NC in P3. unfold IMG_HI, kPtrArrayReserve in P1, P2, P3.
  pose proof (geom_nums _ (hb_hg _ _ _ _ _ QS)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG).
  pose proof (qs_chunk A it i ch rho' QS) as (_ & _ & MS & IH & HTG & _). pose proof (hb_hu _ _ _ _ _ QS) as HUq.
  assert (EP : eval rho' vPTR = Z_to_bv 64 (PAB + 8 * Z.of_nat j)) by (unfold vPTR; cbn [eval]; rewrite KV by (unfold VSCh, VS0h; cbn; tauto); exact E210).
  assert (EE : eval rho' vEND = Z_to_bv 64 (PAB + 8 * NC)) by (unfold vEND; cbn [eval]; rewrite KV by (unfold VSCh, VS0h; cbn; tauto); exact E213).
  assert (EC : eval rho' vCHV = Z_to_bv 64 (sc_map_beg chj)) by (unfold vCHV; cbn [eval]; rewrite KV by (unfold VSCh, VS0h; cbn; tauto); rewrite E211, (maps_nth A j chj Hj); reflexivity).
  assert (ENr : eval rho' vNEAR = Z_to_bv 64 (SegQS_scan.best (firstn j maps) pp)) by (unfold vNEAR; cbn [eval]; rewrite KV by (unfold VSCh, VS0h; cbn; tauto); exact E212).
  pose proof (hb_E A it i ch rho' QS) as (_ & _ & EI & _).
  assert (PP : 0 <= pp < 2 ^ 47) by (unfold pp; rewrite HUq; unfold PG, IMG_HI in *; clear -MS IH HTG TG; lia).
  pose proof (SegQS_scan.best_range (firstn j maps) pp (proj1 PP)) as BR.
  split; [exact EP|]. split; [exact EE|]. split; [exact EC|]. split.
  - rewrite (upd_of_leaf_h rho' k pp (SegQS_scan.best (firstn j maps) pp) (sc_map_beg chj) Hk EI EC ENr BR ltac:(clear -PP; lia) ltac:(clear -MB; lia) HLF).
    f_equal. rewrite <- SegQS_scan.best_snoc. f_equal. rewrite <- (maps_nth A j chj Hj). symmetry. apply firstn_S_nth_Z. unfold maps. rewrite length_map. apply (proj1 (nth_error_Some _ _)). rewrite Hj. discriminate.
  - unfold LFh in HLF. apply Forall_cons_iff in HLF as [F0 _].
    assert (EA : eval rho' (add vPTR (SLit 8)) = Z_to_bv 64 (PAB + 8 * Z.of_nat j + 8)) by (apply ev_add_lit; [exact EP | clear -P1 P2 P3 LT TG; lia | lia | clear -P1 P2 P3 LT TG; lia]).
    assert (EQ : holds rho' EQF <-> S j = length (aa_sec A)).
    { unfold EQF. cbn [holds branch_taken]. unfold bv_eqb. rewrite EA, EE, !u64_lit by (clear -P1 P2 P3 LT TG; lia). rewrite Z.eqb_eq. unfold NC. lia. }
    split; intros EV; rewrite EV in F0.
    + exact (proj1 EQ F0).
    + unfold NC in LT. assert (S j <> length (aa_sec A)) by (intros X; apply F0; exact (proj2 EQ X)). lia.
Qed.

Lemma cell_ro_h : ltac2:(tb__ "0|b|
S20S13S6S46VA;Vit;Vi;Vch;R3A5S0S1aS6A1S3fS6S7VA;A1R3A3S19S6R2A2A3S0S37Q40M0A1M1S23R5S7aA2S36G0S2fVPAB;S31Z8M2S30R4A1A2A2A2A3S0G1S23R6S79A2S36G0S8R4A1A2A3S6aS99SafVTZ;R7A2S15S1dS1dS1dS1dS25S38A2M3S38A2M4S18S1dS1dS38S13A2M5S25A2M6A1M7A2M8S38A2M9S1cG8S38S1cG4G7S1cG3S38S1cS25S38S7aZ0MaA4G2A4S15G6S1cG5S25S1cS38S13GaU8A4S79A4S1bG6A1A3A4S2fVPAB;S31G2S30R6A1A2A2A4S1bG9A1A3A3F_;F_;F_;F_;Fchj;Fj;Fr;").
Proof.
  intros r j chj QS Hj EP EC. destruct (tbl_cell_h A it i ch r j chj QS Hj) as (CP & LT & MB). pose proof (tbl_nums_h A it i ch r QS) as (P1 & P2 & P3 & P4 & _).
  fold PAB in P1, P2, P4. fold NC in P3. unfold IMG_HI, kPtrArrayReserve in P1, P2, P3, P4.
  pose proof (geom_nums _ (hb_hg _ _ _ _ _ QS)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG).
  apply Forall_cons; [|apply Forall_nil]. unfold ro_condW.
  split; [exact EP|]. split; [clear -P1 P2 P3 LT TG; lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [clear -P1; lia|].
  split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|]. split.
  - intros z Hz. exists 0, 8%nat, vCHV, (sc_map_beg chj). split; [left; reflexivity|]. split; [cbn [Z.of_nat]; lia|]. split; [exact EC|]. rewrite Z.add_0_r. exact CP.
  - intros z Hz. apply HTZ_tbl. fold PAB. unfold kPtrArrayReserve. clear -Hz P3 LT. lia.
Qed.

Lemma PIN0_keepsC : ltac2:(tb__ "0|0|
S20S20S3aVA;R2A2S92S91S84A1R3R2A3S3aVA;R3A2F_;F_;Frho';Frho;").
Proof.
  intros rho rho' P0 HKp. apply (PIN0_eq A rho rho' P0). intros v Hv. rewrite (proj2 HKp v (SVar v)); [reflexivity|].
  unfold idm, VSCh. apply in_map_iff. exists v. split; [reflexivity | apply in_or_app; left; exact Hv].
Qed.

Lemma loop_glue_h : ltac2:(tb__ "0|2|
S13S13S20S20S18S37Q40A1A1S81S40S13R6S15S13U1S15S13U3S15S13U5S15S13U7S1bS13A1A3A3A3A3A3S3aVA;R5A2S8cS4eVA;Vit;R8R7A4S47R9S17S6S7VA;A1A2M0A2S92S91S84A1R9R8A3S45S3dVJH;S5dVcf;RcA2R9R8R7A6S4S20S20S1S45S3dVJH;S83Vcf;A1R1RaR9A6S1S3aVA;R1A2S1S4eVA;Vit;S1fRdA1M1R1A4S47G1G0A2A2A2A2Lrho2;A2F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho';Frho;Fj;Fk;").
Proof.
  intros k j rho rho' tp [tr [ms md]] Hk P0 F1 HSC Hj HKp H.
  assert (Hk8 : (k < 8)%nat) by (cbn [In] in Hk; lia). assert (Hodd : Nat.even k = false) by (cbn [In] in Hk; repeat (destruct Hk as [<-|Hk]; [reflexivity|]); destruct Hk).
  destruct (sF_parts nW cf SF) as (_ & _ & _ & _ & _ & LOK & _). destruct (LOK k Hk) as (TOK & ZOK & LASTB).
  pose proof (JF_stable nW UStopLe false A Kc rho1 HUS HKc) as HST. change GW with NPRE in HST.
  pose proof (PIN0_keepsC rho rho' P0 HKp) as P0'.
  destruct (env_at rho' tp tr md (proj2 H) P0') as (QS' & _).
  destruct (nth_error (aa_sec A) j) as [chj|] eqn:Ej; [|exfalso; apply nth_error_None in Ej; lia].
  destruct (leaf_vals_h k j rho rho' tp _ chj Hk8 QS' HSC Ej HKp H) as (EP & EE & EC & EA3 & _ & HLT). specialize (HLT Hodd).
  destruct (nth_error (aa_sec A) (S j)) as [chn|] eqn:En; [|exfalso; apply nth_error_None in En; lia].
  destruct (tbl_cell_h A it i ch rho' (S j) chn QS' En) as (CPn & LTn & MBn).
  pose proof (tbl_nums_h A it i ch rho' QS') as (P1 & P2 & P3 & _). fold PAB in P1, P2. fold NC in P3. unfold IMG_HI, kPtrArrayReserve in P1, P2, P3.
  pose proof (geom_nums _ (hb_hg _ _ _ _ _ QS')) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG).
  set (dsD := [(vPTR, 0, 8, [(0, 8%nat, vCHV)], PAB + 8 * Z.of_nat j)] : list dspec).
  assert (HOBJ : ss_objs (ax_S (lfh cf k)) = keepN (lfh cf k) 1 ++ map dobj dsD) by exact (lastb_sound _ _ LASTB).
  destruct (s_stepW (chunk_sh_zone ch) TZ (JF nW UStopLe false A Kc rho1) HST (zbLh A ch (PAB + 8 * Z.of_nat (S j))) zloS (zhiX (sc_map_size ch)) ZULh
              (zsepLh A it i ch rho' (PAB + 8 * Z.of_nat (S j)) QS' ltac:(clear; lia) ltac:(fold PAB; unfold kPtrArrayReserve; clear -P3 LTn; lia))
              (T_loop_hb nW (lfh cf k) (hf_SC cf) k) dsD [Z_to_bv 64 (sc_map_beg chn)] rho' tp tr ms md TOK HOBJ eq_refl H (cell_ro_h rho' j chj QS' Ej EP EC)) as (rho5 & H5 & V5 & RM5 & AG5 & EV).
  { intros EV3 HJ4. set (rho3 := rho_absorb rho' (map dobj dsD) (vms md tp ms)) in *.
    set (rho4 := rho_sets rho3 (combine (s_bs (T_loop_hb nW (lfh cf k) (hf_SC cf) k)) [Z_to_bv 64 (sc_map_beg chn)])) in *.
    assert (P4 : PIN0 A rho4).
    { apply (PIN0_eq A rho' rho4 P0'). intros v Hv. unfold rho4. rewrite rho_sets_other; [reflexivity|]. cbn. intros [<-|[]]. unfold VS0h, vNXT in Hv. cbn in Hv. intuition discriminate. }
    destruct (env_at rho4 tp tr md HJ4 P4) as (QS4 & _). pose proof (zenv_at rho4 tp tr md HJ4 P4 F1) as ZE4.
    assert (E214 : rw rho4 vNXT = Z_to_bv 64 (sc_map_beg chn)) by (unfold rho4; apply rho_sets_get; [cbn; repeat constructor; cbn; tauto | cbn; tauto]).
    assert (EP4 : eval rho4 vPTR = Z_to_bv 64 (PAB + 8 * Z.of_nat j)) by (rewrite <- EP; unfold vPTR; cbn [eval]; unfold rho4; rewrite rho_sets_other; [reflexivity | cbn; intros [X|[]]; discriminate]).
    destruct (cell_carve_h A it i ch rho4 (add vPTR (SLit 8)) (SVar vNXT) (S j) chn QS4 En
                ltac:(fold PAB; replace (PAB + 8 * Z.of_nat (S j)) with (PAB + 8 * Z.of_nat j + 8) by lia; apply ev_add_lit; [exact EP4 | clear -P1 P2 P3 LTn TG; lia | lia | clear -P1 P2 P3 LTn TG; lia])
                ltac:(cbn [eval]; exact E214)) as (C1 & C2).
    split; [exact C1|]. split; [exact C2|]. split; [exact (zs_L rho4 _ _ ZE4 ZOK)|]. intros _. apply Forall_nil. }
  exists rho5. split; [exact H5|].
  set (rho4 := rho_sets (rho_absorb rho' (map dobj dsD) (vms md tp ms)) (combine (s_bs (T_loop_hb nW (lfh cf k) (hf_SC cf) k)) [Z_to_bv 64 (sc_map_beg chn)])) in *.
  split; [|split; [|exact HLT]].
  - apply (PIN0_eq A rho' rho5 P0'). intros v Hv. rewrite (V5 v (SVar v)).
    + cbn [eval]. unfold rho4. rewrite rho_sets_other; [reflexivity|]. cbn. intros [<-|[]]. unfold VS0h, vNXT in Hv. cbn in Hv. intuition discriminate.
    + unfold T_loop_hb, M_loop_hb. cbn [s_M]. apply in_or_app. left. unfold idm. apply in_map_iff. exists v. split; [reflexivity | exact Hv].
  -
    assert (OT : forall v, v <> vNXT -> rw rho4 v = rw rho' v) by (intros v Hv; unfold rho4; rewrite rho_sets_other; [reflexivity | cbn; intros [X|[]]; congruence]).
    assert (E214 : rw rho4 vNXT = Z_to_bv 64 (sc_map_beg chn)) by (unfold rho4; apply rho_sets_get; [cbn; repeat constructor; cbn; tauto | cbn; tauto]).
    assert (EP4 : eval rho4 vPTR = Z_to_bv 64 (PAB + 8 * Z.of_nat j)) by (rewrite <- EP; unfold vPTR; cbn [eval]; apply OT; discriminate).
    assert (EE4 : eval rho4 vEND = Z_to_bv 64 (PAB + 8 * NC)) by (rewrite <- EE; unfold vEND; cbn [eval]; apply OT; discriminate).
    assert (EA4 : eval rho4 (a3_of k) = Z_to_bv 64 (SegQS_scan.best (firstn (S j) maps) pp)).
    { rewrite <- EA3. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [cbn [a3_of]; unfold vCHV, vNEAR; cbn [eval]; apply OT; discriminate|]). destruct Hk. }
    unfold SCANI. fold PAB. fold NC.
    rewrite (V5 210%positive (add vPTR (SLit 8)) ltac:(unfold T_loop_hb, M_loop_hb; cbn; tauto)), (V5 213%positive vEND ltac:(unfold T_loop_hb, M_loop_hb; cbn; tauto)),
            (V5 212%positive (a3_of k) ltac:(unfold T_loop_hb, M_loop_hb; cbn; tauto)), (V5 211%positive (SVar vNXT) ltac:(unfold T_loop_hb, M_loop_hb; cbn; tauto)).
    split; [replace (PAB + 8 * Z.of_nat (S j)) with (PAB + 8 * Z.of_nat j + 8) by lia; apply ev_add_lit; [exact EP4 | clear -P1 P2 P3 LTn TG; lia | lia | clear -P1 P2 P3 LTn TG; lia]|].
    split; [exact EE4|]. split; [exact EA4|]. cbn [eval]. rewrite E214, (maps_nth A (S j) chn En). reflexivity.
Qed.

Let G : ageom := aa_geom A.
Let h : Z := sc_map_beg ch.
Let msz : Z := sc_map_size ch.
Lemma zs_E : ltac2:(tb__ "0|0|
S20S14S6S18S22A1S6fVnW;VA;Vp;Vn;Vch;R4A6S0S14S6eVnW;S4cR4A1R2A3S16A3S41S22S57S6dR6S4dVA;Vi;Vch;R4A4S49S4bS9Vch;A1A1S4cR5A1A5R3S70VnW;R3A2A5F_;F_;Fobjs;Flst;Fl;Fr;").
Proof. intros r l lst objs ZE HB. apply (zds_sound nW A p n ch r (zbE A i ch lst) zloS (zhiX (sc_map_size ch)) (ZUXl l)); try (repeat split; reflexivity); [exact ZE | exact HB]. Qed.

Lemma exit_glue_h : ltac2:(tb__ "0|3|
S13S14S13S6S87S20S20S18S37Q40A1A1S81S40S13R9S15S13U0S15S13U2S15S13U4S15S13U6S1bS13A1A3A3A3A3A3S5fVnW;Vcf;Vf;R9R6A5S3aVA;R6A2S8cS4eVA;Vit;RbR8A4S47RcS17S6S7VA;A1M0A2M1A2S92S91S84A1RaR9A3S45S3dVJH;S5dVcf;R10A2RaR9R8A6S0S1aS6A1S3fS6G0S44G1U1A2M2A3S19S6ReA2A3S3S0S14R11S16A3S0S13Vi;G2A3A2S4S20S20S1S45S3dVJH;S85R10A1R1RdRcA6S1S3aVA;R1A2S4fVA;Vi;Vch;R13R11R1S7bA7A2A2Lrho2;A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho';Frho;Fcv;Flst;Fj;Fl;Fk;").
Proof.
  intros k l j lst cv rho rho' tp [tr [ms md]] Hk SV P0 F1 HSC Hj HKp H Hl HLI.
  assert (Hk8 : (k < 8)%nat) by (cbn [In] in Hk; lia). assert (Hev : Nat.even k = true) by (cbn [In] in Hk; repeat (destruct Hk as [<-|Hk]; [reflexivity|]); destruct Hk).
  destruct (sV_parts nW cf f l cv SV k Hk) as (XSEL & XLX & XLD & TOK & ZOK).
  pose proof (JF_stable nW UStopLe false A Kc rho1 HUS HKc) as HST. change GW with NPRE in HST.
  pose proof (PIN0_keepsC rho rho' P0 HKp) as P0'.
  destruct (env_at rho' tp tr md (proj2 H) P0') as (QS' & _ & _ & _ & SEPS).
  destruct (nth_error (aa_sec A) j) as [chj|] eqn:Ej; [|exfalso; apply nth_error_None in Ej; lia].
  destruct (leaf_vals_h k j rho rho' tp _ chj Hk8 QS' HSC Ej HKp H) as (EP & EE & EC & EA3 & HEQ & _). specialize (HEQ Hev).

  pose proof (qs_chunk A it i ch rho' QS') as (_ & _ & MS & IH & HTG & _). fold h msz in MS, IH, HTG. pose proof (hb_hu _ _ _ _ _ QS') as HUq. fold h in HUq.
  assert (EH : eval rho' (a3_of k) = Z_to_bv 64 h).
  { rewrite EA3. f_equal. rewrite HEQ. unfold maps. rewrite <- (length_map sc_map_beg), firstn_all.
    apply (chunk_is_best (aa_sec A) i ch pp (hb_hi _ _ _ _ _ QS')); [unfold pp; fold h msz; rewrite HUq; unfold PG; clear -MS; lia | fold h; unfold IMG_HI in IH; clear -IH; lia | |].
    - pose proof QS' as [_ _ _ _ _ _ _ _ HSEP _ _ _ _]. destruct HSEP as (_ & _ & _ & _ & HJx). exact HJx.
    - intros j' ch' Hj'. pose proof QS' as [_ _ _ _ HSR _ _ _ _ _ _ _ _]. destruct HSR as (SC1 & _).
      destruct (SC1 j' ch' Hj') as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _). destruct D10 as (_ & D & _). exact D. }
  destruct (proj2 H) as (HK & HCB & HRM & HFRM). cbn [w_tr w_cfg cfg_model fst snd] in HK, HCB, HRM, HFRM.
  pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite HI; discriminate)) as LTi.
  assert (HLF : l = false -> (i < length (aa_sec A) - 1)%nat).
  { intros ->. destruct (Nat.eq_dec i (length (aa_sec A) - 1)) as [Ex|NE]; [pose proof (proj2 HLI Ex); discriminate | clear -NE LTi; lia]. }

  pose proof (SPA_axforms segsA JH _ rho' _ _ tp _ XSEL H) as Hx.
  pose proof (zenv_at rho' tp tr md (proj2 H) P0' F1) as ZE'.
  destruct (dissolveZW (chunk_sh_zone ch) TZ (JF nW UStopLe false A Kc rho1) HTZ_sh (Lx_hb (lfh cf k))
              (firstn (length (ss_objs (ax_S (Lx_hb (lfh cf k)))) - 1) (ss_objs (ax_S (Lx_hb (lfh cf k))))) [O_sh] rho' tp tr ms md (lastb_sound _ _ XLX) Hx) as (Hd & RWd & RLd).
  { intros x (o & Ho & Hz). destruct Ho as [<-|[]]. rewrite (rng_sh nW A p n ch rho' ZE') in Hz. cbn [fst snd] in Hz.
    destruct ZE' as [_ _ _ _ _ _ _ _ _ (B1 & B2 & B3 & B4 & B5 & B6 & B7)].
    assert (M8 : sc_map_beg ch mod 8 = 0).
    { destruct (proj1 (Z.mod_divide (sc_map_beg ch) 4096 ltac:(clear; lia)) B3) as [q Eq]. rewrite Eq. replace (q * 4096) with (q * 512 * 8) by (clear; lia). apply Z_mod_mult. }
    assert (M8' : (sc_map_beg ch + 6144) mod 8 = 0) by (rewrite Z.add_mod, M8 by (clear; lia); reflexivity).
    rewrite <- (Sh_add8 (sc_map_beg ch + 6144) (N8 n) M8' B6) in Hz. unfold chunk_sh_zone, Sh in *.
    pose proof (Z.div_le_mono (sc_map_beg ch) (sc_map_beg ch + 6144) 8 ltac:(clear; lia) ltac:(clear; lia)) as D1.
    pose proof (Z.div_le_mono (sc_map_beg ch + 6144 + N8 n) (sc_map_beg ch + sc_map_size ch) 8 ltac:(clear; lia) ltac:(clear -B7; lia)) as D2.
    clear -Hz D1 D2. lia. }
  { constructor; [left; reflexivity | constructor]. }
  set (rho2 := rho_absorb rho' [O_sh] (vms md tp ms)) in *.
  change (SPA segsA JH (Ld_hb (lfh cf k)) rho2 tp (tr, mkCfg ms md)) in Hd.
  assert (P2 : PIN0 A rho2) by (apply (PIN0_eq A rho' rho2 P0'); intros v _; apply RWd).
  destruct (env_at rho2 tp tr md (proj2 Hd) P2) as (QS2 & _).
  assert (EP2 : eval rho2 vPTR = Z_to_bv 64 (PAB + 8 * Z.of_nat j)) by (rewrite <- EP; unfold vPTR; cbn [eval]; apply RWd).
  assert (EC2 : eval rho2 vCHV = Z_to_bv 64 (sc_map_beg chj)) by (rewrite <- EC; unfold vCHV; cbn [eval]; apply RWd).
  set (dsD := [(vPTR, 0, 8, [(0, 8%nat, vCHV)], PAB + 8 * Z.of_nat j)] : list dspec).
  set (vals := [Z_to_bv 64 msz] ++ (if l then [] else [Z_to_bv 64 (Z.of_nat i); Z_to_bv 64 (sc_map_beg lst); Z_to_bv 64 (NC - 1)])).
  set (TX := T_exit_hb nW (lfh cf k) (hv_SX cv) f k l) in *.
  assert (LV : length vals = length (s_bs TX)) by (unfold vals, TX, T_exit_hb, BSX; destruct l; reflexivity).
  assert (NDB : List.NoDup (map fst (combine (s_bs TX) vals))) by (unfold vals, TX, T_exit_hb, BSX; destruct l; cbn; repeat constructor; cbn; intuition discriminate).
  assert (INB : forall v, In v (map fst (combine (s_bs TX) vals)) -> In v [203; 204; 205; 206]%positive) by (intros v; unfold vals, TX, T_exit_hb, BSX; destruct l; cbn; tauto).
  assert (HOBJ : ss_objs (ax_S (s_C TX)) = keepN (s_C TX) (s_k TX) ++ map dobj dsD) by exact (lastb_sound _ _ XLD).
  destruct (s_stepUW (chunk_sh_zone ch) TZ (JF nW UStopLe false A Kc rho1) HST (zbE A i ch lst) zloS (zhiX msz) (ZUXl l)
              (zsepE_h A it i ch rho2 l lst QS2 (SEPS _ lst Hl) Hl HLF)
              TX (UX (a3_of k)) ZDU dsD vals rho2 tp tr ms md TOK HOBJ LV Hd (cell_ro_h rho2 j chj QS2 Ej EP2 EC2)) as (rho5 & H5 & V5 & RM5 & AG5 & EV).
  { intros EV3 HJ4. set (rho3 := rho_absorb rho2 (map dobj dsD) (vms md tp ms)) in *.
    set (rho4 := rho_sets rho3 (combine (s_bs TX) vals)) in *.
    assert (OT : forall v, ~ In v [203; 204; 205; 206]%positive -> rw rho4 v = rw rho' v) by (intros v Hv; unfold rho4; rewrite rho_sets_other; [exact (RWd v) | intros X; exact (Hv (INB v X))]).
    assert (P4 : PIN0 A rho4).
    { apply (PIN0_eq A rho' rho4 P0'). intros v Hv. apply OT. unfold VS0h in Hv. cbn in Hv. cbn [In]. clear -Hv. intuition (subst; discriminate). }
    destruct (env_at rho4 tp tr md HJ4 P4) as (QS4 & _ & _ & _ & SEPS4). pose proof (zenv_at rho4 tp tr md HJ4 P4 F1) as ZE4.
    assert (XV4 : XVALS A i ch l lst rho4 (a3_of k)).
    { split; [transitivity (eval rho' (a3_of k)); [|exact EH]; rewrite a3_hv; cbn [eval]; apply OT; cbn [In]; destruct k as [|[|[|[|k]]]]; cbn [hv_of]; clear; intuition discriminate|].
      split; [unfold rho4; apply rho_sets_get; [exact NDB | unfold vals, TX, T_exit_hb, BSX; destruct l; cbn; tauto]|].
      split; [intros Ex; exact (proj1 HLI Ex)|]. intros Ex. split; [exact (HLF Ex)|]. subst l.
      split; [unfold rho4; apply rho_sets_get; [exact NDB | cbn; tauto]|]. split; [unfold rho4; apply rho_sets_get; [exact NDB | cbn; tauto] | unfold rho4; apply rho_sets_get; [exact NDB | cbn; tauto]]. }
    destruct (exit_carve_h A it i ch rho4 l lst (a3_of k) QS4 (SEPS4 _ lst Hl) Hl XV4) as (C1 & C2).
    destruct (exit_zones_hb A it i ch rho4 rho4 l lst (a3_of k) QS4 (SEPS4 _ lst Hl) Hl P4 XV4) as (C3 & C4).
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact (zs_E rho4 l lst _ ZE4 ZOK)|]. intros _.
    rewrite a3_hv in XV4. exact (exit_facts_h A it i ch rho4 f l lst (hv_of k) Hf QS4 HFAM XV4). }
  exists rho5. split; [exact H5|].
  set (rho4 := rho_sets (rho_absorb rho2 (map dobj dsD) (vms md tp ms)) (combine (s_bs TX) vals)) in *.
  assert (OT : forall v, ~ In v [203; 204; 205; 206]%positive -> rw rho4 v = rw rho' v) by (intros v Hv; unfold rho4; rewrite rho_sets_other; [exact (RWd v) | intros X; exact (Hv (INB v X))]).
  split.
  - apply (PIN0_eq A rho' rho5 P0'). intros v Hv. rewrite (V5 v (SVar v)).
    + cbn [eval]. apply OT. unfold VS0h in Hv. cbn in Hv. cbn [In]. clear -Hv. intuition (subst; discriminate).
    + unfold TX, T_exit_hb, M_exit_hb. cbn [s_M]. apply in_or_app. left. unfold idm. apply in_map_iff. exists v. split; [reflexivity | exact Hv].
  - unfold XVALS. fold h. fold msz. unfold vH. cbn [eval].
    rewrite (V5 202%positive (a3_of k) ltac:(unfold TX, T_exit_hb, M_exit_hb; cbn [s_M]; apply in_or_app; right; cbn; tauto)).
    rewrite (V5 203%positive vMS ltac:(unfold TX, T_exit_hb, M_exit_hb; cbn [s_M]; apply in_or_app; right; cbn; tauto)).
    split; [transitivity (eval rho' (a3_of k)); [|exact EH]; rewrite a3_hv; cbn [eval]; apply OT; cbn [In]; destruct k as [|[|[|[|k]]]]; cbn [hv_of]; clear; intuition discriminate|].
    split; [unfold vMS; cbn [eval]; unfold rho4; apply rho_sets_get; [exact NDB | unfold vals, TX, T_exit_hb, BSX; destruct l; cbn; tauto]|].
    split; [intros Ex; exact (proj1 HLI Ex)|]. intros Ex. split; [exact (HLF Ex)|]. subst l.
    rewrite (V5 204%positive vIDX ltac:(unfold TX, T_exit_hb, M_exit_hb; cbn [s_M]; apply in_or_app; right; apply in_or_app; right; cbn; tauto)).
    rewrite (V5 205%positive vLAST ltac:(unfold TX, T_exit_hb, M_exit_hb; cbn [s_M]; apply in_or_app; right; apply in_or_app; right; cbn; tauto)).
    rewrite (V5 206%positive vLIDX ltac:(unfold TX, T_exit_hb, M_exit_hb; cbn [s_M]; apply in_or_app; right; apply in_or_app; right; cbn; tauto)).
    unfold vIDX, vLAST, vLIDX. cbn [eval].
    split; [unfold rho4; apply rho_sets_get; [exact NDB | cbn; tauto]|]. split; [unfold rho4; apply rho_sets_get; [exact NDB | cbn; tauto] | unfold rho4; apply rho_sets_get; [exact NDB | cbn; tauto]].
Qed.

Definition hbnums : Prop := ltac2:(tb__ "0|0|
S1S4S20S20S46VA;Vit;Vi;Vch;R1A5Lr0;A2S13S6S0S1aS6A1S3fS6S7VA;A1R2A3S19S6R1A2A3S3bVA;R3R2A3F_;Fchj;Fj;A2").
Lemma hbnums_at : ltac2:(tb__ "0|0|
S20S18S37Q40A1A1S18S97A1S96VJH;R4R3R2R1A4S3aVA;R5A2S8fF_;F_;Fmd;Ftr;Ftp;Fr;").
Proof. intros r tp tr md HJ P0. destruct (env_at r tp tr md HJ P0) as (QS & _ & _ & _ & SEPS). split; [exists r; exact QS | exact SEPS]. Qed.
Definition XVALSh (l : bool) (lst : sec_chunk) (r : valuation) : Prop := ltac2:(tb__ "0|2|
S1S0S37Q40M0A1M1S21Vr;PcaA2S36G0S8Vch;A1A2A3S1S0G1S21Vr;PcbA2S36G0S9Vch;A1A2A3S0S14Vl;S1eA3S1S0G1S21Vr;PccA2S36G0S30Vi;A1A2A3S1S0G1S21Vr;PcdA2S36G0S8Vlst;A1A2A3S0G1S21Vr;PceA2S36G0S35S30S17S6S7VA;A1A2A1Z1A2A2A3A2A2F_;A2A2").
Definition ENV0s (r : valuation) : Prop := PIN0 A r.
Definition ENVXs (l : bool) (lst : sec_chunk) (r : valuation) : Prop := ltac2:(tb__ "0|0|
S1S3aVA;Vr;A2S90Vl;Vlst;Vr;A3A2").

Lemma ENV0s_keep : ltac2:(tb__ "0|0|
S20S20S8eR2A1S92S91S89A1R3R2A3S8eR3A1F_;F_;Fr';Fr;").
Proof. intros r r' P0 [_ HM]. apply (PIN0_eq A r r' P0). intros v Hv. rewrite (HM v (SVar v)); [reflexivity|]. unfold idm. apply in_map_iff. exists v. split; [reflexivity | exact Hv]. Qed.
Lemma ENVXs_keep : ltac2:(tb__ "0|0|
S14S6S20S20S8dR4R3R2A3S39S40S39R1S8aA3S0S37Q40A1S21R4R2A2S21R5R2A2A3F_;Fv;S8dR6R5R3A3F_;F_;Fr';Fr;Flst;Fl;").
Proof.
  intros l lst r r' (P0 & X1 & X2 & X3) HK. split; [apply (PIN0_eq A r r' P0); intros v Hv; apply HK; unfold VSXh; apply in_or_app; left; exact Hv|].
  unfold XVALSh. rewrite !HK by (unfold VSXh, VS0h; cbn; tauto). split; [exact X1 | split; [exact X2 | exact X3]].
Qed.
Lemma HLF_of : ltac2:(tb__ "0|1|
S14S3S0S14R1S16A3S0S13Vi;S44S17S6S7VA;A1A2U1A2M0A3A2S0S14R2S1eA3S47Vi;G0A2F_;F_;Fl;").
Proof.
  intros l HLI ->. pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite HI; discriminate)) as LTi.
  destruct (Nat.eq_dec i (length (aa_sec A) - 1)) as [Ex|NE]; [pose proof (proj2 HLI Ex); discriminate | clear -NE LTi; lia].
Qed.
Lemma XVALSh_XVALS : ltac2:(tb__ "0|0|
S14S6S20S3S0S14R3S16A3S0S13Vi;S44S17S6S7VA;A1A2U1A2A3A2S90R4R3R2A3S4fVA;Vi;Vch;R5R4R3S7bA7F_;F_;Fr;Flst;Fl;").
Proof.
  intros l lst r HLI (X1 & X2 & X3). split; [exact X1|]. split; [exact X2|]. split; [intros Ex; exact (proj1 HLI Ex)|].
  intros Ex. split; [exact (HLF_of l HLI Ex) | exact (X3 Ex)].
Qed.
Lemma zsepE_hb : ltac2:(tb__ "0|4|
S8fS14S6S0S1aS6A1S3fS6S7VA;A1M0S44S17S6G0A2U1A2M1A3S19S6R1A2A3S3S0S14R3S16A3S0S13Vi;G1A3A2S13S13S40S13R2S4cR6A1A3S40S13R2S4cR7A1A3S5S0S13R4R3A3A1S2S2eS2fS4dVA;Vi;Vch;R8R5A5M2S4bVmsz;R5A2A2S2fS4dVA;Vi;Vch;R8R4A5M3S49R4A1A2A2S2eS2fG3S4bVmsz;R4A2A2S2fG2S49R5A1A2A2A2F_;F_;F_;Fz';Fz;F_;F_;Flst;Fl;F_;").
Proof. intros ((r0 & QS0) & SEPS) l lst Hl HLI. exact (zsepE_h A it i ch r0 l lst QS0 (SEPS _ lst Hl) Hl (HLF_of l HLI)). Qed.
Lemma exit_zones_hb2 : ltac2:(tb__ "0|2|
S8fS14S6S20S0S1aS6A1S3fS6S7VA;A1M0S44S17S6G0A2U1A2M1A3S19S6R2A2A3S3S0S14R4S16A3S0S13Vi;G1A3A2S8dR5R4R3A3S41S22S57S6dR4S4dVA;Vi;Vch;R5A4S49S4bVmsz;A1S4cR6A1A5S7dR6S7bA2S15S57S51S54R6A1A3A5F_;F_;F_;Fr;Flst;Fl;F_;").
Proof.
  intros ((r0 & QS0) & SEPS) l lst r Hl HLI (P0 & XV). rewrite <- NX_OBJ2.
  destruct (exit_zones_hb A it i ch r0 r l lst vH QS0 (SEPS _ lst Hl) Hl P0 (XVALSh_XVALS l lst r HLI XV)) as (C3 & C4). constructor; [exact C3 | exact C4].
Qed.

Context {Q : assn} (X : trk Q).
Hypothesis HJX : JOK X JH.

Section ScanH.
Variables (l : bool) (lst : sec_chunk) (cv : hbvar) (tp : list word).
Hypothesis Hl : ltac2:(tb__ "0|1|
S0S1aS6A1S3fS6S7VA;A1M0S44S17S6G0A2U1A2A3S19S6Vlst;A2A3").
Hypothesis HLI : ltac2:(tb__ "0|0|
S3S0S14Vl;S16A3S0S13Vi;S44S17S6S7VA;A1A2U1A2A3A2").
Hypothesis SV : ltac2:(tb__ "0|0|
S5fVnW;Vcf;Vf;Vl;Vcv;A5").

Hypothesis HXC : ltac2:(tb__ "0|0|
S20S3aVA;R1A2S4fVA;Vi;Vch;Vl;Vlst;R2S7bA7S93VQ;VX;S45S3dVJH;S85Vcv;A1R3Vtp;A5A3F_;F_;Frho2;").

Lemma scan_loop_h : ltac2:(tb__ "0|1|
S13S13S20S0S13R3S44S44S17S6S7VA;A1A2M0U1A2R2A2A3S47R3G0A2S3aVA;R3A2S8cS4eVA;Vit;R6R5A4S93VQ;VX;S45S3dVJH;S83Vcf;A1R6Vtp;A5A3F_;F_;F_;F_;F_;Frho;Fj;Fm;").
Proof.
  destruct (sF_parts nW cf SF) as (LEN & _).
  induction m as [|m IH]; intros j rho Hm Hj P0 F1 HSC; apply (seg_PL X Elf f cf FOK JH rho tp HJX); intros Lf rho' HIN HKp;
    destruct (leaf_k cf Lf LEN HIN) as (k & Hk & ->); destruct (Nat.even k) eqn:Ev.
  - assert (Hk' : In k [0; 2; 4; 6]%nat) by (do 8 (destruct k as [|k]; [first [discriminate Ev | cbn; tauto]|]); exfalso; clear -Hk; lia).
    apply (tr_glue X _ JH (hv_SX cv) tp (fun r => PIN0 A r /\ XVALS A i ch l lst r vH)).
    + intros w Hw. destruct (exit_glue_h k l j lst cv rho rho' tp w Hk' SV P0 F1 HSC Hj HKp Hw Hl HLI) as (rho2 & H2 & K2 & X2).
      exists rho2. split; [exact H2 | split; [exact K2 | exact X2]].
    + intros r [R1 R2]. exact (HXC r R1 R2).
  -
    assert (Hk' : In k [1; 3; 5; 7]%nat) by (do 8 (destruct k as [|k]; [first [discriminate Ev | cbn; tauto]|]); exfalso; clear -Hk; lia).
    apply (tr_pure X _ False); [|intros []]. intros w Hw.
    destruct (loop_glue_h k j rho rho' tp w Hk' P0 F1 HSC Hj HKp Hw) as (_ & _ & _ & _ & LT). clear -LT Hm. lia.
  - assert (Hk' : In k [0; 2; 4; 6]%nat) by (do 8 (destruct k as [|k]; [first [discriminate Ev | cbn; tauto]|]); exfalso; clear -Hk; lia).
    apply (tr_glue X _ JH (hv_SX cv) tp (fun r => PIN0 A r /\ XVALS A i ch l lst r vH)).
    + intros w Hw. destruct (exit_glue_h k l j lst cv rho rho' tp w Hk' SV P0 F1 HSC Hj HKp Hw Hl HLI) as (rho2 & H2 & K2 & X2).
      exists rho2. split; [exact H2 | split; [exact K2 | exact X2]].
    + intros r [R1 R2]. exact (HXC r R1 R2).
  -
    assert (Hk' : In k [1; 3; 5; 7]%nat) by (do 8 (destruct k as [|k]; [first [discriminate Ev | cbn; tauto]|]); exfalso; clear -Hk; lia).
    apply (tr_glue X _ JH (hf_SC cf) tp (fun r => PIN0 A r /\ SCANI A it (S j) r /\ (S j < length (aa_sec A))%nat)).
    + intros w Hw. destruct (loop_glue_h k j rho rho' tp w Hk' P0 F1 HSC Hj HKp Hw) as (rho2 & H2 & K2 & S2 & L2). exists rho2. tauto.
    + intros r (R1 & R2 & R3). apply (IH (S j) r); [clear -Hm R3; lia | exact R3 | exact R1 | exact F1 | exact R2].
Qed.

Theorem scan_all_h : ltac2:(tb__ "0|0|
S20S3aVA;R1A2S93VQ;VX;S45S3dVJH;S82Vcf;A1R2Vtp;A5A3F_;Frho;").
Proof.
  intros rho P0.
  apply (tr_glue X _ JH (hf_SC cf) tp (fun r => PIN0 A r /\ SCANI A it 0 r /\ FCH1)).
  - intros w Hw. destruct (first_glue_h rho tp w P0 Hw) as (rho2 & H2 & K2 & S2 & F2). exists rho2. tauto.
  - intros r (R1 & R2 & R3). pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite HI; discriminate)) as LTi.
    apply (scan_loop_h (length (aa_sec A) - 1 - 0) 0 r eq_refl ltac:(clear -LTi; lia) R1 R3 R2).
Qed.
End ScanH.

Theorem G_scan_hb : ltac2:(tb__ "0|2|
S14S6S87S18S37Q40A1A1S0S1aS6A1S3fS6S7VA;A1M0S44S17S6G0A2U1A2M1A3S19S6R3A2A3S3S0S14R5S16A3S0S13Vi;G1A3A2S5fVnW;Vcf;Vf;R6R4A5S20S8dR8R7R1A3S93VQ;VX;S45S3dVJH;S85R7A1R2R6A5A3F_;Fr4;S20S8eR1A1S93VQ;VX;S45S3dVJH;S82Vcf;A1R2R7A5A3F_;Fr;F_;F_;F_;F_;Ftp;Fcv;Flst;Fl;").
Proof.
  intros l lst cv tp Hl HLI SV HC r P0. apply (scan_all_h l lst cv tp Hl HLI SV); [|exact P0].
  intros rho2 P2 (X1 & X2 & _ & X4). apply HC. split; [exact P2|]. split; [exact X1|]. split; [exact X2|]. intros Ex. exact (proj2 (X4 Ex)).
Qed.

End LoopH.
End F0A_hbN_scan.

(* [comment removed for export] *)
Module CallocHit0E.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineCallocI2"; "rho_c"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@Corelib.Init.Logic"; "False"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "JLc_ok"; "Lc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1"; "E_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "E3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "J_alloc_preT"; "KcA"; "Kc_ok"; "Pre_callocI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI"; "Jc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Stdlib.Lists.List"; "In"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "mul"; "pow"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP RebuildM SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ci.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS5i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.SpineCallocS6i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS7i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS8i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocS9i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ci.CallocHit0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bl.SpineCallocEi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bl.SpineCallocEc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineCallocS5t OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cf.CallocHitTail0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dc.CallocHitTail0E OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ap.CertCallocS1c OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertCallocS1e OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS1i.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS12i.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section HIT0E.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S0S7VCST;R1A2S7S1fR2A2S11F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S0S7VCST;R1A2S13S20R2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S1aVAInv;VW;Vst;VA;VKc;S5PcA1A6").
Let law_die : forall A rho tp md, AInv A rho tp md -> cell_ok (view segs (rm rho)) (mkACell 0x182f1c 4 0) := AInvA_die.
Let W0 : list ulink := Wcan 0.
Let st0 : ustop := UStopLe.

Theorem ecalloc_hit_0_P : ltac2:(tb__ "0|5|
S1eS1bS4SbSaQ40M0A1A1SbSdSeSfA2M1A1S10Vsegs;S14S8R3A1R2R1A5S2S24G1ScSeSfS16VW0;Vst0;A2S15VCST;VXGL;R6R5A4A4R2A3S1cR6A1S25S26S9G0S3R6PcM2A2A2S9G0S3R6PdA2A2A2S27Z2M3Z40A2A2S12S0S22R9S9G0S3S8R7A1G2A2A2A2Z0A3S4S1Vsegs;S6Vsegs;S23VW0;Vst0;RbRaS8R9A1A5M4S18VW0;Vst0;G3A3R1R8A5R6A3FrhoE;F_;S4S1Vsegs;S6Vsegs;G4S17VW0;Vst0;G3Z8A4R1R8A5R6A3FrhoE;S1Vsegs;S6Vsegs;S21VW0;Vst0;RbRaA4S1dS19VW0;Vst0;A3R9R8A5R6A3F_;F_;F_;F_;F_;TQ;FPosts;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Posts Q HPin HKc Hmul HREF HSEC.
  pose proof HUS_c as HUS.
  assert (HW : stopJ_w W0 st0) by (hw_discharge).
  apply (espine_s1c 0%nat st0 2 law_die WC1_0 DC1_0 WE1_c DE1_c HSW_c HUS_c Wa_c Da_c Wb_c Fbh_c Fbl_c ENTh_c ENTl_c NXhi_c NXlo_c s1_ecert_0 A Kc rho tp Q HKc Hmul); [|exact HSEC].
  intros rhoE1.
  apply (espine_s2c 0%nat st0 2 OVa_0 OVb_0 TABa_0 TABb_0 Wa'_0 Wb'_0 Da'_0 Db'_0 NXa_0 NXb_0 Fa_0 Fb_0 Ga_0 Gb_0 SKa_0 SKb_0 XXa_0 XXb_0 XFa_0 XFb_0
           W1a_0 W1ba_0 W1ca_0 W2a_0 W1ra_0 W2ra_0 W1b_0 W1bb_0 W1cb_0 W2b_0 W1rb_0 W2rb_0 sa_0 sra_0 sb_0 srb_0 ENTa_0 ENTra_0 ENTb_0 ENTrb_0
           SIDa_0 SIDra_0 SIDb_0 SIDrb_0 FB_0 FBr_0 NXC1g_0 s2_ecert_0 A Kc (rho_c rho) tp Q HW HUS HKc).
  2: { intros Hz0 rhoE2. apply (espine_s3r 0%nat st0 2 NXC2r_0 s3r_ecert_0 A Kc (rho_c rho) tp Q HUS HKc). exact (HREF Hz0). }
  intros rhoE2.
  apply (espine_s3p_cert 0%nat st0 2 NXC2p_0 s3p_ecert_0 A Kc (rho_c rho) tp Q HUS HKc).
  exact (ecalloc_hit_tail_0_P CST XGL HCST HXGL HCSTM HCSTD A Kc (rho_c rho) tp Posts HPin HKc).
Qed.
End HIT0E.
End CallocHit0E.

(* [comment removed for export] *)
Module CallocHit1E.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineCallocI2"; "rho_c"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@Corelib.Init.Logic"; "False"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "JLc_ok"; "Lc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1"; "E_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "E3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "J_alloc_preT"; "KcA"; "Kc_ok"; "Pre_callocI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI"; "Jc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Stdlib.Lists.List"; "In"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "mul"; "pow"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP RebuildM SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ct.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS5iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS6iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.SpineCallocS7iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS8iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocS9iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ct.CallocHit1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bl.SpineCallocEiW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bl.SpineCallocEc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineCallocS5t OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cu.CallocHitTail1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dc.CallocHitTail1E OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ap.CertCallocS1c OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertCallocS1e OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS1iW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS12iW1.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section HIT0E.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S0S7VCST;R1A2S7S1fR2A2S11F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S0S7VCST;R1A2S13S20R2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S1aVAInv;VW;Vst;VA;VKc;S5PcA1A6").
Let law_die : forall A rho tp md, AInv A rho tp md -> cell_ok (view segs (rm rho)) (mkACell 0x182f1c 4 0) := AInvA_die.
Let W0 : list ulink := Wcan 1.
Let st0 : ustop := UStopLeOrPc.

Theorem ecalloc_hit_1_P : ltac2:(tb__ "0|5|
S1eS1bS4SbSaQ40M0A1A1SbSdSeSfA2M1A1S10Vsegs;S14S8R3A1R2R1A5S2S24G1ScSeSfS16VW0;Vst0;A2S15VCST;VXGL;R6R5A4A4R2A3S1cR6A1S25S26S9G0S3R6PcM2A2A2S9G0S3R6PdA2A2A2S27Z2Z40A2A2S12S0S22R9S9G0S3S8R7A1G2A2A2A2Z0A3S4S1Vsegs;S6Vsegs;S23VW0;Vst0;RbRaS8R9A1A5M3S18VW0;Vst0;Z3M4A3R1R8A5R6A3FrhoE;F_;S4S1Vsegs;S6Vsegs;G3S17VW0;Vst0;G4Z8A4R1R8A5R6A3FrhoE;S1Vsegs;S6Vsegs;S21VW0;Vst0;RbRaA4S1dS19VW0;Vst0;A3R9R8A5R6A3F_;F_;F_;F_;F_;TQ;FPosts;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Posts Q HPin HKc Hmul HREF HSEC.
  pose proof HUS_c as HUS.
  assert (HW : stopJ_w W0 st0) by (hw_discharge).
  apply (espine_s1c_pc 1%nat st0 3 law_die WC1_0 DC1_0 WE1_c DE1_c HSW_c HUS_c Wa_c Da_c Wb_c Fbh_c Fbl_c ENTh_c ENTl_c NXpc_c s1_ecert_1 Est_c WPC_c DPC_c HWne_c A Kc rho tp Q HKc Hmul); [|exact HSEC].
  intros rhoE1.
  apply (espine_s2c 1%nat st0 3 OVa_0 OVb_0 TABa_0 TABb_0 Wa'_0 Wb'_0 Da'_0 Db'_0 NXa_0 NXb_0 Fa_0 Fb_0 Ga_0 Gb_0 SKa_0 SKb_0 XXa_0 XXb_0 XFa_0 XFb_0
           W1a_0 W1ba_0 W1ca_0 W2a_0 W1ra_0 W2ra_0 W1b_0 W1bb_0 W1cb_0 W2b_0 W1rb_0 W2rb_0 sa_0 sra_0 sb_0 srb_0 ENTa_0 ENTra_0 ENTb_0 ENTrb_0
           SIDa_0 SIDra_0 SIDb_0 SIDrb_0 FB_0 FBr_0 NXC1g_0 s2_ecert_0 A Kc (rho_c rho) tp Q HW HUS HKc).
  2: { intros Hz0 rhoE2. apply (espine_s3r 1%nat st0 3 NXC2r_0 s3r_ecert_0 A Kc (rho_c rho) tp Q HUS HKc). exact (HREF Hz0). }
  intros rhoE2.
  apply (espine_s3p_cert 1%nat st0 3 NXC2p_0 s3p_ecert_0 A Kc (rho_c rho) tp Q HUS HKc).
  exact (ecalloc_hit_tail_1_P CST XGL HCST HXGL HCSTM HCSTD A Kc (rho_c rho) tp Posts HPin HKc).
Qed.
End HIT0E.
End CallocHit1E.

(* [comment removed for export] *)
Module SegQIF_glue.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "nat"; "cons"; "bool"; "length"; "list"; "app"; "nil"; "prod"; "true"; "fst"; "pair"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "sobj"; "sprop"; "rm"; "valuation"; "holds"; "sprop_eqb"; "ss_facts"; "ss_objs"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "to_nat"; "of_nat"; "mul"; "@Stdlib.Lists.List"; "In"; "Forall2"; "NoDup"; "combine"; "existsb"; "forallb"; "tl"; "@Corelib.Init.Nat"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "cs_cache"; "qbatch"; "class_state"; "cs_allocated_user"; "cs_free_array"; "cs_mapped_free_array"; "cs_mapped_user"; "AA"; "aa_geom"; "aa_cache_inited"; "aa_q_global"; "aa_q_thread"; "ag_ctx"; "ag_spacebeg"; "mkQB"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "cell_ok"; "mkACell"; "bview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_mdefs"; "BSM"; "ZUM"; "zhiM"; "N_M"; "TQPs"; "zbM"; "FFM"; "VSM"; "ZD_K"; "ZD_M"; "m_S0"; "mcert"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel"; "drain_grows"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip"; "zloQ"; "DQI0"; "N_rti"; "O_ishQ"; "carve_okq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_env"; "qienvF"; "N_itmF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "it_cls"; "it_ab"; "@Stdlib.PArith.BinPos.Pos"; "le"; "of_nat"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "region_info"; "Size"; "free_array"; "max_count"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "pre_facts"; "top_high"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states"; "DEPTH_R"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cy.SegQIF_glue.KeptM"; "zbMq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "cls_of"; "QW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS"; "idxs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones"; "in_zone"; "zdesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv"; "JRI"; "QP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith"; "vb_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cy.SegQIF_glue"; "REFOBJ_K"; "valsM"; "nodupPb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue"; "forallb2"; "keepN"; "same_rng"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQIF_defs"; "TQPf";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cy.SegQIF_glue.EntryM"; "ENVM"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQIF_env SegQIF_mdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dt.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.SegQS_k OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvQ9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SegQF_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQIP_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQIF_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_mdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dt.SegQIF_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma Forall_map_in {X Y : Type} : ltac2:(tb__ "0|0|
VY;OF_;VX;VY;F_;SbVX;A1VX;S22VX;R1R2A3R5R4R2A1A1F_;Fx;S2cVY;R4S2bVX;VY;R3R2A4A3F_;Fl;Ff;FP;").
Proof. intros P f l H. apply Forall_forall. intros y Hy. apply in_map_iff in Hy as (x & <- & Hx). exact (H x Hx). Qed.
Lemma In_idxs : ltac2:(tb__ "0|0|
S5S7S22S7R1S6bR2A1A3S50R2S1fR3A1A2F_;Fi;Fn;").
Proof. intros n i H. unfold idxs in H. apply in_seq in H. lia. Qed.

Section CarveM.
Variables (Kc : KcA) (A : AA) (r : valuation) (tp : list word) (tr : list event) (md : Model).
Hypothesis HKc : Kc_ok Kc.
Hypothesis HK : ltac2:(tb__ "0|0|
S6eVKc;VA;Vr;Vtp;Vtr;Vmd;A6").
Hypothesis HCI : aa_cache_inited A = true.
Variables (c n : Z).
Hypothesis Hc : 1 <= c <= 30.
Hypothesis Hn : ltac2:(tb__ "0|0|
S0S5S6fVc;A1Vn;A3").
Let G : ageom := aa_geom A.
Let T : Z := ag_thread G.
Let SB : Z := ag_spacebeg G.
Let cs : class_state := cls_of A c.
Let m : bview := ltac2:(tb__ "0|0|
S40S2aS17Vr;A1A2").
Hypothesis HFULL : ltac2:(tb__ "0|0|
S0S5S20SaS5S2eVcs;A1A2A1S61Vc;A1A3").
Hypothesis EV : ltac2:(tb__ "0|3|
S1S0S13Q40M0A1M1S14Vr;Pc8A2S12G0Vc;A2A3S1S0G1S14Vr;Pc9A2S12G0S5fVc;A1A2A3S1S0G1S14Vr;PddA2S12G0S20SaS5S32Vcs;A1A2A1A2A3S1S0G1S14Vr;PdeA2S12G0S33Vcs;A1A2A3S1S0G1S14Vr;PdfA2S12G0S31Vcs;A1A2A3S1S0G1S14Vr;Pe0A2S12G0S34Vcs;A1A2A3S1S0G1S14Vr;Pe1A2S12G0S5eVSB;Vc;A2A2A3S7S50R1S1fVn;A1M2A2S0G1S14Vr;S5cS29Ue7R2A2A1A2S12G0S2dS5S29G2R2A2S2eVcs;A1Z0A4A2A3F_;Fi;A2A2A2A2A2A2A2").

Lemma ri_zero_cellsM : ltac2:(tb__ "0|3|
S1S41Vm;S42S1dS5eVSB;Vc;A2M0Z28A2U8M1Z0M2A3A2S1S41Vm;S42S1dG0Z38A2G1G2A3A2S41Vm;S42S1dG0Z44A2U1G2A3A2A2A2").
Proof.
  destruct HK as (HA & _). pose proof HA as (HG & _ & _ & HRest & _). cbn zeta in HRest. destruct HRest as (_ & _ & R3 & _).
  destruct R3 as (_ & _ & _ & P4). pose proof (P4 c Hc) as HC. unfold class_repr in HC. cbn zeta in HC.
  destruct HC as (_ & _ & _ & _ & C5 & _ & C7 & C8 & _). unfold RI_allocated_meta, RI_mapped_meta, RI_exhausted in *. fold G SB in C5, C7, C8.
  pose proof kSpaceSize_val as KSV.
  assert (ZRI : forall z, region_info SB c <= z < region_info SB c + kRegionInfoStride -> maskv (fs_footb G) m z = m z).
  { intros z Hz. apply (MS A m HG). fold G SB. unfold region_info, kRegionInfoStride in Hz. rewrite KSV in *. lia. }
  split; [|split]; (eapply (cell_tr A m); [|eassumption]); intros k Hk; apply ZRI; cbn [c_addr c_w] in *; unfold kRegionInfoStride; lia.
Qed.

Lemma carve_M : ltac2:(tb__ "0|0|
S9S0S9S51Vc;Vcs;A2R1A3S2cS3eS56Vr;A1S47Vn;R2A2A3F_;Fg;").
Proof using All.
  intros g HGR. pose proof (K0_laws Kc HKc) as HL.
  destruct (kq_facts segsA (K0 Kc) HL A r tp _ _ HK) as [HG HRIG HRTC _ HST _ HCLS _ _ _ _ _ _]. fold G in HG, HRIG, HRTC, HST, HCLS.
  destruct HRIG as (E151 & E152 & E155 & E156). fold T SB in E151, E155, E156, HST.
  pose proof (HCLS HCI c Hc) as CV. fold cs in CV.
  pose proof (cv_count _ _ _ _ _ CV) as C_cnt. pose proof (cv_max _ _ _ _ _ CV) as C_max. pose proof (cv_size _ _ _ _ _ CV) as C_sz.
  pose proof (cv_ri_mutex _ _ _ _ _ CV) as R0. pose proof (cv_ri_nfreed _ _ _ _ _ CV) as R16. pose proof (cv_ri_mfa _ _ _ _ _ CV) as R24. pose proof (cv_ri_au _ _ _ _ _ CV) as R32.
  pose proof (cv_ri_mu _ _ _ _ _ CV) as R48. pose proof (cv_ri_present _ _ _ _ _ CV) as PRI. pose proof (cv_fa_bounds _ _ _ _ _ CV) as (FB1 & FB2 & FB3). pose proof (cv_fa_present _ _ _ _ _ CV) as PFA.
  pose proof (cv_chunks _ _ _ _ _ CV) as C_chk.
  destruct ri_zero_cellsM as (R40 & R56 & R68).
  destruct (kchunks_facts c Hc) as (K1 & K2 & _). rewrite Hn in K1, K2.
  unfold pc_entry, RI_mutex, RI_num_freed, RI_mapped_free_array, RI_allocated_user, RI_mapped_user in *. fold G T SB in C_cnt, C_max, C_sz, C_chk, R0, R16, R24, R32, R48, PRI, PFA.
  rewrite HFULL in C_cnt. rewrite <- K2 in C_cnt, C_max, HFULL.
  destruct EV as (E200 & E201 & E221 & E222 & E223 & E224 & E225 & ECH).
  pose proof (geom_nums _ HG) as (_ & _ & _ & T0 & T1 & _ & C0 & C1' & _ & _ & S1 & S2 & S16 & TG). fold G T SB in T0, T1, S1, S2, S16.
  pose proof (geom_bands _ HG) as (_ & _ & _ & _ & TI & CI & _). fold G T in TI. unfold IMG_LO, IMG_HI in TI, CI. unfold HIGH_SHADOW_END in S1. rewrite kSpaceSize_val in S2.
  pose proof (Zle_0_nat (length (cs_free_array cs))) as NF0. unfold kFreeArraySize, kFreeArrayMapSize in *.
  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side.size_ok_all c Hc) as (SZ1 & SZ2).
  assert (HR : cells_ok (view segsA (rm r)) (rtc_cells RTC_A (aa_geom A))) by exact HRTC.
  assert (TBLK : forall lo hi, T <= lo -> hi <= T + 4096 -> (hi <= 0x10000 \/ 0x646000 <= lo)) by (intros lo hi B1 B2; clear -TI B1 B2; lia).
  assert (EcbC : eval r cbC = Z_to_bv 64 (T + 208)) by (unfold cbC; apply ev_add_lit; [unfold vT; cbn [eval]; exact E151 | lia | lia | lia]).
  assert (Eent : bv_unsigned (eval r entQ) = T + 208 + 80 * c).
  { unfold entQ, add. rewrite U_add, U_mul. fold (add vT (SLit 208)). fold cbC. rewrite EcbC. cbn [eval]. rewrite E200, !u64_lit by lia. unfold M64v.
    rewrite (Z.mod_small (c * 80)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (RIv : region_info SB c = SB + 2 ^ 37 + 128 * c) by (unfold region_info, kRegionInfoStride; rewrite kSpaceSize_val; lia).
  assert (ERI : bv_unsigned (eval r vRI) = region_info SB c) by (unfold vRI; cbn [eval]; rewrite E225, u64_lit by lia; reflexivity).
  assert (FAv : free_array SB c = SB + c * 2 ^ 32 + 3758096384) by (unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize; lia).
  unfold N_M. apply Forall_app. split; [|apply Forall_app; split; [|apply Forall_app; split]].
  -
    clear C_cnt C_max C_sz C_chk R0 R16 R24 R32 R48 PRI PFA R40 R56 R68 EcbC Eent ERI ECH. unfold SB, T, G in *.
    destruct g; unfold XROs, pgbS, cfcS, cfbS; repeat apply Forall_cons; try apply Forall_nil; unfold carve_okq; lazy beta iota zeta; cbn [eval]; rewrite ?u64_lit by lia; unfold PG in *.
    all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|].
    all: split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
    all: split; [intros off Hoff; split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]|].
    all: unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; cbn [eval]; civ_any2 HR.
  -
    unfold PCS, chkS, mcS, cntS, szMS. repeat apply Forall_cons; try apply Forall_nil; unfold carve_okq; lazy beta iota zeta; rewrite Eent.
    all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|].
    + split; [unfold cells_inside, chk_cells; apply Forall_map_in; intros i Hi; apply In_idxs in Hi; cbn; lia|]. split.
      * intros off Hoff. set (i := Z.to_nat ((off - 16) / 4)).
        assert (Hi : (i < length (cs_cache cs))%nat) by (unfold i; pose proof (Z.div_lt_upper_bound (off - 16) 4 (2 * n) ltac:(lia) ltac:(lia)); pose proof (Z.div_pos (off - 16) 4 ltac:(lia) ltac:(lia)); lia).
        destruct (nth_error (cs_cache cs) i) as [x|] eqn:EX; [|apply nth_error_None in EX; lia].
        pose proof (Z.div_mod (off - 16) 4 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (off - 16) 4 ltac:(lia)) as MB.
        eapply (cell_wok_rd2 _ _ _ _ _ (C_chk i x EX)); cbn [Z.of_nat]; unfold i; try (rewrite Z2Nat.id by (apply Z.div_pos; lia)); try lia; try (apply TBLK; lia).
      * unfold cells_in_view, chk_cells. apply Forall_map_in. intros i Hi. apply In_idxs in Hi. intros j Hj.
        destruct (nth_error (cs_cache cs) (Z.to_nat n + i)) as [x|] eqn:EX; [|apply nth_error_None in EX; lia].
        pose proof (nth_error_nth _ _ 0 EX) as EN.
        apply (civ_cell r (rm r) (T + 208 + 80 * c) (16 + 4 * (n + Z.of_nat i)) 4 x (vCHq i));
          [replace (T + 208 + 80 * c + (16 + 4 * (n + Z.of_nat i))) with (T + 208 + 80 * c + 16 + 4 * Z.of_nat (Z.to_nat n + i)) by lia; exact (C_chk _ x EX)
          | unfold vCHq; cbn [eval]; rewrite (ECH i Hi), EN; reflexivity | lia | lia | exact Hj].
    + split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|]. split.
      * intros off Hoff. eapply (cell_wok_rd2 _ _ _ _ _ C_max); cbn [Z.of_nat]; try lia; try (apply TBLK; lia).
      * unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
        intros j Hj. apply (civ_cell r (rm r) (T + 208 + 80 * c) 4 4 (2 * n) (SLit (2 * n))); [exact C_max | reflexivity | lia | lia | exact Hj].
    + split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|]. split.
      * intros off Hoff. eapply (cell_wok_rd2 _ _ _ _ _ C_cnt); cbn [Z.of_nat]; try lia; try (apply TBLK; lia).
      * unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
        intros j Hj. apply (civ_cell r (rm r) (T + 208 + 80 * c) 0 4 (2 * n) (SLit (2 * n))); [replace (T + 208 + 80 * c + 0) with (T + 208 + 80 * c) by lia; exact C_cnt | reflexivity | lia | lia | exact Hj].
    + split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|]. split.
      * intros off Hoff. eapply (cell_wok_rd2 _ _ _ _ _ C_sz); cbn [Z.of_nat]; try lia; try (apply TBLK; lia).
      * unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
        intros j Hj. apply (civ_cell r (rm r) (T + 208 + 80 * c) 8 8 (Size c) (SVar 201)); [exact C_sz | cbn [eval]; exact E201 | lia | lia | exact Hj].
  -
    unfold riMS. apply Forall_cons; [|apply Forall_nil]. unfold carve_okq; lazy beta iota zeta. rewrite ERI.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|]. split.
    + intros off Hoff. apply (wr_present (rm r) (region_info SB c) (region_info SB c + 128) (region_info SB c + off) PRI); [lia | lia | lia | right; lia].
    + unfold cells_in_view, vNF, vMFA, vAU. repeat apply Forall_cons; try apply Forall_nil; intros j Hj.
      * apply (civ_cell r (rm r) (region_info SB c) 0 8 0 (SLit 0)); [exact R0 | reflexivity | lia | lia | exact Hj].
      * apply (civ_cell r (rm r) (region_info SB c) 16 8 (Z.of_nat (length (cs_free_array cs))) (SVar 221)); [exact R16 | cbn [eval]; exact E221 | lia | lia | exact Hj].
      * apply (civ_cell r (rm r) (region_info SB c) 24 8 (cs_mapped_free_array cs) (SVar 222)); [exact R24 | cbn [eval]; exact E222 | lia | lia | exact Hj].
      * apply (civ_cell r (rm r) (region_info SB c) 32 8 (cs_allocated_user cs) (SVar 223)); [exact R32 | cbn [eval]; exact E223 | lia | lia | exact Hj].
      * apply (civ_cell r (rm r) (region_info SB c) 40 8 0 (SLit 0)); [exact R40 | reflexivity | lia | lia | exact Hj].
      * apply (civ_cell r (rm r) (region_info SB c) 48 8 (cs_mapped_user cs) (SVar 224)); [exact R48 | cbn [eval]; exact E224 | lia | lia | exact Hj].
      * apply (civ_cell r (rm r) (region_info SB c) 56 8 0 (SLit 0)); [exact R56 | reflexivity | lia | lia | exact Hj].
      * apply (civ_cell r (rm r) (region_info SB c) 68 1 0 (SLit 0)); [exact R68 | reflexivity | lia | lia | exact Hj].
  - destruct g; [apply Forall_nil|]. apply Forall_cons; [|apply Forall_nil].
    unfold drain_grows in HGR. apply Z.ltb_ge in HGR. rewrite Hn in HGR.
    assert (Edst : bv_unsigned (eval r dstM) = free_array SB c + 4 * Z.of_nat (length (cs_free_array cs))).
    { unfold dstM. rewrite U_add, U_add, U_add, !U_sll_lit. unfold vSB, vNF. cbn [eval]. rewrite E200, E155, E221, !u64_lit by lia. change (32 mod 64) with 32. change (2 mod 64) with 2.
      unfold M64v. rewrite (Z.mod_small (c * 2 ^ 32)) by lia. rewrite (Z.mod_small (c * 2 ^ 32 + 3758096384)) by lia. rewrite (Z.mod_small (SB + (c * 2 ^ 32 + 3758096384))) by lia.
      rewrite (Z.mod_small (Z.of_nat (length (cs_free_array cs)) * 2 ^ 2)) by lia. rewrite Z.mod_small by lia. rewrite FAv. lia. }
    unfold carve_okq. lazy beta iota zeta. rewrite Edst. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [unfold cells_inside; apply Forall_nil|]. split; [|unfold cells_in_view; apply Forall_nil].
    intros off Hoff. apply (wr_present (rm r) _ _ (free_array SB c + 4 * Z.of_nat (length (cs_free_array cs)) + off) PFA); [lia | lia | lia | right; lia].
Qed.
Lemma inz_M : ltac2:(tb__ "0|0|
S9S9S5S5S5S5S5S0S9S51Vc;Vcs;A2R7A3S23S15S6dS6cVr;S49VT;R6VSB;R5R4R3S1dS1dVT;Zd0A2S21Z50Vc;A2A2R2S60VSB;Vc;A2A9S52S46S45R7A1A5S2bS3eS15S3fS47Vn;R8A2A4S4dVn;R8A2A5F_;FSHU;FTOP;Fab;Fu;FCTX;Fvb;Fg;").
Proof using All.
  intros g vb CTX u ab TOP SHU HGR. pose proof (K0_laws Kc HKc) as HL.
  destruct (kq_facts segsA (K0 Kc) HL A r tp _ _ HK) as [HG HRIG _ _ _ _ HCLS _ _ _ _ _ _]. fold G in HG, HRIG, HCLS.
  destruct HRIG as (E151 & E152 & E155 & E156). fold T SB in E151, E155, E156.
  pose proof (HCLS HCI c Hc) as CV. fold cs in CV. pose proof (cv_fa_bounds _ _ _ _ _ CV) as (FB1 & FB2 & FB3).
  destruct (kchunks_facts c Hc) as (K1 & K2 & _). rewrite Hn in K1, K2.
  destruct EV as (E200 & E201 & E221 & E222 & E223 & E224 & E225 & ECH).
  pose proof (geom_nums _ HG) as (_ & _ & _ & T0 & T1 & _ & C0 & C1' & _ & _ & S1 & S2 & S16 & TG). fold G T SB in T0, T1, S1, S2, S16.
  unfold HIGH_SHADOW_END in S1. rewrite kSpaceSize_val in S2. pose proof (Zle_0_nat (length (cs_free_array cs))) as NF0. unfold kFreeArraySize, kFreeArrayMapSize in *.
  assert (EcbC : eval r cbC = Z_to_bv 64 (T + 208)) by (unfold cbC; apply ev_add_lit; [unfold vT; cbn [eval]; exact E151 | lia | lia | lia]).
  assert (Eent : bv_unsigned (eval r entQ) = T + 208 + 80 * c).
  { unfold entQ, add. rewrite U_add, U_mul. fold (add vT (SLit 208)). fold cbC. rewrite EcbC. cbn [eval]. rewrite E200, !u64_lit by lia. unfold M64v.
    rewrite (Z.mod_small (c * 80)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (RIv : region_info SB c = SB + 2 ^ 37 + 128 * c) by (unfold region_info, kRegionInfoStride; rewrite kSpaceSize_val; lia).
  assert (ERI : bv_unsigned (eval r vRI) = region_info SB c) by (unfold vRI; cbn [eval]; rewrite E225, u64_lit by lia; reflexivity).
  assert (FAv : free_array SB c = SB + c * 2 ^ 32 + 3758096384) by (unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize; lia).
  assert (UZ : forall z, In z [0; 5; 7; 12]%nat -> In z (ZUM vb)) by (intros z Hz; destruct vb; cbn in Hz |- *; tauto).
  unfold N_M, ZD_M. rewrite !map_app. apply Forall2_app; [|apply Forall2_app; [|apply Forall2_app]].
  - destruct g; unfold XROs, ZD_XRO, pgbS, cfcS, cfbS; cbn [map carve_obj]; repeat apply Forall2_cons; try apply Forall2_nil; unfold in_zone.
    all: split; [apply UZ; cbn; tauto|]. all: split; [cbn; lia|]. all: split; [cbn; lia|]. all: right.
    all: unfold carved; rewrite obj_range_mk by lia; cbn [fst snd eval zbM zbQ]; rewrite u64_lit by lia; lia.
  - unfold PCS, ZD_PC, chkS, mcS, cntS, szMS. cbn [map carve_obj]. repeat apply Forall2_cons; try apply Forall2_nil; unfold in_zone.
    all: split; [apply UZ; cbn; tauto|]. all: split; [cbn; lia|]. all: split; [cbn; lia|]. all: right.
    all: unfold carved; rewrite obj_range_mk by lia; cbn [fst snd zbM zbQ]; rewrite Eent; lia.
  - unfold riMS. cbn [map carve_obj]. apply Forall2_cons; [|apply Forall2_nil]. unfold in_zone.
    split; [apply UZ; cbn; tauto|]. split; [cbn; lia|]. split; [cbn; lia|]. right.
    unfold carved. rewrite obj_range_mk by lia. cbn [fst snd zbM zbQ]. rewrite ERI, RIv. lia.
  - destruct g; cbn [map carve_obj]; [apply Forall2_nil|]. apply Forall2_cons; [|apply Forall2_nil]. unfold in_zone.
    unfold drain_grows in HGR. apply Z.ltb_ge in HGR. rewrite Hn in HGR.
    assert (Edst : bv_unsigned (eval r dstM) = free_array SB c + 4 * Z.of_nat (length (cs_free_array cs))).
    { unfold dstM. rewrite U_add, U_add, U_add, !U_sll_lit. unfold vSB, vNF. cbn [eval]. rewrite E200, E155, E221, !u64_lit by lia. change (32 mod 64) with 32. change (2 mod 64) with 2.
      unfold M64v. rewrite (Z.mod_small (c * 2 ^ 32)) by lia. rewrite (Z.mod_small (c * 2 ^ 32 + 3758096384)) by lia. rewrite (Z.mod_small (SB + (c * 2 ^ 32 + 3758096384))) by lia.
      rewrite (Z.mod_small (Z.of_nat (length (cs_free_array cs)) * 2 ^ 2)) by lia. rewrite Z.mod_small by lia. rewrite FAv. lia. }
    split; [apply UZ; cbn; tauto|]. split; [cbn; lia|]. split; [cbn; lia|]. right.
    unfold carved. rewrite obj_range_mk by lia. cbn [fst snd zbM zbQ]. rewrite Edst. lia.
Qed.

Lemma facts_M : ltac2:(tb__ "0|1|
S9S0S9S51Vc;Vcs;A2R1A3S64VA;Vr;A2S2cS16S19Vr;A1M0S63S65A1A3S2cS16G0S4aVn;R4A2A3F_;F_;F_;Fg;").
Proof using All.
  intros g HGR HTOP HFp. pose proof (K0_laws Kc HKc) as HL.
  destruct (kq_facts segsA (K0 Kc) HL A r tp _ _ HK) as [HG HRIG _ _ _ _ HCLS _ _ _ _ _ _]. fold G in HG, HRIG, HCLS.
  destruct HRIG as (E151 & E152 & E155 & E156). fold T SB in E151, E155, E156.
  pose proof (HCLS HCI c Hc) as CV. fold cs in CV. pose proof (cv_fa_bounds _ _ _ _ _ CV) as (FB1 & FB2 & FB3).
  destruct (kchunks_facts c Hc) as (K1 & K2 & _). rewrite Hn in K1, K2.
  destruct EV as (E200 & E201 & E221 & E222 & E223 & E224 & E225 & ECH).
  pose proof (geom_nums _ HG) as (_ & _ & _ & T0 & T1 & TP & _ & _ & _ & _ & S1 & S2 & S16 & TG). fold G T SB in T0, T1, TP, S1, S2, S16.
  unfold HIGH_SHADOW_END in S1. rewrite kSpaceSize_val in S2. pose proof (Zle_0_nat (length (cs_free_array cs))) as NF0. unfold kFreeArraySize, kFreeArrayMapSize, PG in *.
  destruct (stk_facts A r HTOP HFp) as (HD & HT2 & HSP). cbv zeta in HD, HT2, HSP.
  assert (RIv : region_info SB c = SB + 2 ^ 37 + 128 * c) by (unfold region_info, kRegionInfoStride; rewrite kSpaceSize_val; lia).
  assert (E4 : eval r (SAlu ALU_SLL (SAlu ALU_ADD vNF (SLit n)) (SLit 2)) = Z_to_bv 64 (4 * (Z.of_nat (length (cs_free_array cs)) + n))).
  { apply bv_eq. rewrite U_sll_lit. change (2 mod 64) with 2. change (SAlu ALU_ADD vNF (SLit n)) with (add vNF (SLit n)).
    rewrite (ev_add_lit r vNF (Z.of_nat (length (cs_free_array cs))) n ltac:(unfold vNF; cbn [eval]; exact E221) ltac:(lia) ltac:(lia) ltac:(lia)). rewrite !u64_lit by lia. unfold M64v. rewrite Z.mod_small by lia. lia. }
  unfold drain_grows in HGR. rewrite Hn in HGR.
  unfold FFM. repeat apply Forall_cons; try apply Forall_nil.
  - cbn [holds]. split; [lia|]. rewrite E225, RIv, u64_lit by lia. change (2 ^ 7) with 128.
    pose proof (Z.div_mod SB (2 ^ 16) ltac:(lia)) as DS. rewrite S16 in DS.
    replace (SB + 2 ^ 37 + 128 * c) with ((512 * (SB / 2 ^ 16) + 2 ^ 30 + c) * 128) by lia. apply Z.mod_mul. lia.
  - cbn [holds]. unfold vNF. cbn [eval]. rewrite E221, !u64_lit by lia. lia.
  - cbn [holds]. split; [lia|]. rewrite E222, u64_lit by lia. change (2 ^ 18) with 262144. exact FB1.
  - cbn [holds]. unfold vMFA. cbn [eval]. rewrite E222, !u64_lit by lia. lia.
  - destruct g; unfold F_grow, F_fast; cbn [holds branch_taken]; unfold bv_ltu; rewrite E4; unfold vMFA; cbn [eval]; rewrite E222, !u64_lit by lia.
    + exact HGR.
    + intros X0. rewrite X0 in HGR. discriminate HGR.
  - cbn [holds eval]. rewrite u64_lit by lia. unfold G in TG. clear - HT2 HD TG. lia.
Qed.
End CarveM.

Definition REFOBJ_K (vb : bool) : list sobj := ltac2:(tb__ "0|0|
ScS15S1cS6aS53A1A1ScS15S2bS3eS15S3fS54A4ScS15S2bS3eS15S3fS28S3eS58Vvb;A1A2A4S8S15S55SdS15A1A3A3A3A3").
Lemma TQPs_ref : ltac2:(tb__ "0|0|
S9S0S9S78S15S15S7aS79S48R1A1U1A2S73R1A1A5SfA3Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma TQPs_pre : ltac2:(tb__ "0|0|
S9S0S9S27S16S16S26S16S1aR1A1S1bS6aS48R2A1A1A1A3Lf;S63S65A1A3SfA3Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition ALLZ : list nat := ltac2:(tb__ "0|0|
S8S7U0S8S7U1S8S7U2S8S7U3S8S7U4S8S7U5S8S7U6S8S7U7S8S7U8S8S7U9SdS7A1A3A3A3A3A3A3A3A3A3A3").

Lemma qienvF_agreeV : ltac2:(tb__ "0|0|
S35SeS5S5A2S18S18S5S5S57R6R5R4R2R1A5S6S5dR1Pd8A2S0S13Q40A1S14R6R2A2S14R7R2A2A3F_;Fi;S0S43S40S2aS17R5A1A2S40S2aS17R6A1A2A3S57R9R8R6R5R4A5F_;F_;F_;Fst;Ft;Fr';Fr;Fit;FA;").
Proof.
  intros A it r r' t st [Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13 Q14 Q15 Q16 Q17] HRW HRM.
  constructor; rewrite ?HRM; try assumption.
  - destruct Q4 as (E151 & E152 & E155 & E156). repeat split; rewrite HRW by lia; assumption.
  - unfold QIV in *. cbv zeta in *. destruct Q6 as (E165 & E200 & E201 & E202 & E203 & E204 & E205 & E206 & E207 & E209 & E210).
    repeat split; rewrite HRW by lia; assumption.
Qed.

Section KeptM.
Variables (A : AA) (it : Z * Z) (r : valuation) (t st : Z).
Hypothesis QE : ltac2:(tb__ "0|0|
S57VA;Vit;Vr;Vt;Vst;A5").
Let T : Z := ag_thread (aa_geom A).
Let SB : Z := ag_spacebeg (aa_geom A).
Let c : Z := it_cls it.
Definition zbMq : nat -> Z := ltac2:(tb__ "0|2|
S49VT;S3aS36VA;A1M0A1VSB;S10S5S5Vit;A3M1S5aVit;A1S3dG0A1S1dS1dVT;Zd0A2S21Z50Vc;A2A2S62G1A1S60VSB;Vc;A2A9").

Lemma inz_K : ltac2:(tb__ "0|0|
S9S64VA;Vr;A2S2cS16S19Vr;A1S63S65A1A3S23S15S6dS6cVr;S66S52S46S45R3A1A5S73R3A1S4cR3A1A5F_;F_;Fvb;").
Proof.
  intros vb HTOP HFp.
  apply (in_zone_ext_list r (zbQ T (ag_ctx (aa_geom A)) SB (fst it) (it_ab it) (topG (aa_geom A)) (T + 208 + 80 * c) (T + 208 + 80 * c) (Sh (fst it))) zloQ zhiQ (if vb then ALLZ else removelast ALLZ)).
  - unfold REFOBJ_K, ZD_K. apply Forall2_app; [|apply Forall2_app].
    + apply (inz_fixF A it r); [destruct vb; cbn; tauto | destruct vb; cbn; tauto | exact HTOP | exact HFp].
    + apply (inz_rtiF A it r t st QE); destruct vb; cbn; tauto.
    + pose proof (inz_itmF A it r t st QE vb (if vb then ALLZ else removelast ALLZ) ltac:(intros z Hz; destruct vb; cbn in Hz |- *; tauto) ltac:(intros ->; cbn; tauto)) as X.
      unfold N_itmF, ZD_itmF in X. cbn [map app] in X. apply Forall2_cons_iff in X as [_ X].
      pose proof (inz_ishF A it r t st QE (if vb then ALLZ else removelast ALLZ) ltac:(destruct vb; cbn; tauto)) as Y.
      pose proof (Forall2_app X Y) as XY. unfold N_itmF. destruct vb; cbn [tl app map] in XY |- *; exact XY.
  - unfold ZD_K, ZD_fix, ZD_rti. destruct vb; cbn [app]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; (split; [cbn; tauto | split; [reflexivity | split; reflexivity]]).
Qed.

Lemma zsepMq : ltac2:(tb__ "0|2|
S9S0S9R1S72Vit;A1A3S7S7S22S7R2S45R4A1A3S22S7R2S45R5A1A3S2S0S7R4R3A3A1S3S1eS1dS66R5A1M0S46R5A1A2S1dS66R4A1M1S52R4A1A2A2S1eS1dG1S46R4A1A2S1dG0S52R5A1A2A2A2F_;F_;F_;Fz';Fz;F_;Fvb;").
Proof.
  intros vb EVB. pose proof QE as [HG HSEP3 HRTC HRIG HGEO HV HCV HIM HSTAT Ht Hst HNF HQP HAU HIN HPR HMU]. unfold qgeo in HGEO.
  pose proof (qf_nums A it r t st QE) as (T0 & T1 & C0 & C1' & S14 & TG & K16). pose proof (qf_Sh A it r t st QE) as (SH0 & SH1 & L0 & L1).
  pose proof (qf_wins A it r t st QE) as (WTI & WCI & WTB & WCB & WTC & WTS & WCS).
  destruct HGEO as (C1 & Z1 & Z2 & RZ & RZ16 & EU & N1 & R1 & M1 & U1 & A16 & UN & TOP & S1 & S2 & S3 & N8a & N8b).
  assert (HVB : vb = true -> it_ab it + 16 <= fst it - 16).
  { intros X. rewrite EVB in X. unfold vb_of in X. apply negb_true_iff in X. apply Z.eqb_neq in X. unfold it_ab in *.
    pose proof (Z.div_mod (rz (snd it)) 16 ltac:(lia)) as DD. rewrite RZ16 in DD. clear - X RZ DD EU. lia. }
  assert (FAv : free_array SB c = SB + c * 2 ^ 32 + 3758096384) by (unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize; lia).
  intros z z' Hz Hz' NE. unfold zbMq.
  apply (zsepM T (ag_ctx (aa_geom A)) SB (fst it) (it_ab it) (topG (aa_geom A)) (T + 208 + 80 * c) (Sh (fst it)) (free_array SB c)) with (vb := vb); try assumption;
    clear WTI WCI WTB WCB WTC WTS WCS HVB; unfold kUserSpaceSize, kRegionSize, kFreeArraySize, c, T, SB, it_ab in *; rewrite ?FAv; lia.
Qed.
End KeptM.

Lemma BSM_range : ltac2:(tb__ "0|0|
S5S6S1S1eZ0R2A2S1eR2Z8A2A2S22S6R2S44R3A1A3S3S1S5bPddR3A2S5bR3Pe1A2A2S1S5bPe7R3A2S5bR3PeeA2A2A2F_;F_;Fv;Fn;").
Proof.
  intros n v Hn Hv. unfold BSM in Hv. apply in_app_or in Hv as [Hv|Hv].
  - left. cbn in Hv. lia.
  - right. apply in_map_iff in Hv as (i & <- & Hi). apply In_idxs in Hi. lia.
Qed.
Fixpoint nodupPb (l : list positive) : bool := match l with [] => true | x :: t => negb (existsb (Pos.eqb x) t) && nodupPb t end.
Lemma nodupPb_sound : ltac2:(tb__ "0|0|
SbS6A1S0S9S75R1A1SfA3S24S6R2A2F_;Fl;").
Proof.
  induction l as [|x t IH]; intros H; [constructor|]. cbn in H. apply andb_prop in H as [H1 H2]. constructor; [|exact (IH H2)].
  intros Hin. apply negb_true_iff in H1. assert (X : existsb (Pos.eqb x) t = true) by (apply existsb_exists; exists x; split; [exact Hin | apply Pos.eqb_refl]). congruence.
Qed.
Lemma BSM_nodup : ltac2:(tb__ "0|0|
S5S1S1eZ0R1A2S1eR1Z8A2A2S24S6S44R2A1A2F_;Fn;").
Proof.
  intros n Hn. assert (E : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8) by lia.
  repeat (destruct E as [->|E]); try subst n; apply nodupPb_sound; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Lemma combine_map_fst {X Y : Type} : ltac2:(tb__ "0|1|
SbVX;A1M0SbVY;A1S0S7SaVY;R1A2SaVX;R2A2A3S0G0S2bSeVX;VY;A2VX;S10VX;VY;A2S25VX;VY;R3R2A4A4R3A3F_;Fv;Fl;").
Proof. induction l as [|x l IH]; intros [|y v] H; cbn in *; try reflexivity; try discriminate. f_equal. apply IH. lia. Qed.
Definition valsM (n : Z) (cs : class_state) (ri : Z) : list word := ltac2:(tb__ "0|2|
ScS13Q40M0A1M1S8G1S12G0S20SaS5S32Vcs;A1A2A1A2S8G1S12G0S33Vcs;A1A2S8G1S12G0S31Vcs;A1A2S8G1S12G0S34Vcs;A1A2S8G1S12G0Vri;A2SdG1A1A3A3A3A3A3S2bS7G1S7S12G0S2dS5S29S1fVn;A1R1A2S2eVcs;A1Z0A4A2Li;S6bVn;A1A4A3").
Lemma valsM_len : ltac2:(tb__ "0|0|
S5S30S5S0S7SaS13Q40A1S74R3R2R1A3A2SaS6S44R3A1A2A3Fri;Fcs;Fn;").
Proof. intros. unfold valsM, BSM. rewrite !length_app, !length_map. reflexivity. Qed.
Lemma valsM_chunk : ltac2:(tb__ "0|2|
S5S30S5S7S50R1S1fR4A1A2S22SeS6S13Q40M0A1M1A2S11S6G1S5cS29Ue7R2A2A1S12G0S2dS5S29S1fR5A1R2A2S2eR4A1Z0A4A2A4S25S6G1S44R5A1S74R5R4R3A3A4A3F_;Fi;Fri;Fcs;Fn;").
Proof.
  intros n cs ri i Hi. unfold BSM, valsM. cbn [app combine]. do 5 right.
  assert (X : forall l : list nat, In i l -> In (Pos.of_nat (231 + i), Z_to_bv 64 (nth (Z.to_nat n + i) (cs_cache cs) 0))
                (combine (map (fun i0 => Pos.of_nat (231 + i0)) l) (map (fun i0 => Z_to_bv 64 (nth (Z.to_nat n + i0) (cs_cache cs) 0)) l))).
  { induction l as [|j l IH]; intros Hl; [destruct Hl|]. cbn [map combine]. destruct Hl as [->|Hl]; [left; reflexivity | right; exact (IH Hl)]. }
  apply X. unfold idxs. apply in_seq. lia.
Qed.

Section EntryM.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variables (A0 : AA) (rho0 : valuation).
Variables (n : Z) (g vb : bool) (D : mdata).
Hypothesis HC : ltac2:(tb__ "0|0|
S4fVn;Vg;Vvb;VD;A4").

Definition ENVM (A : AA) (c : Z) (r : valuation) : Prop := ltac2:(tb__ "0|3|
S67VA;Vc;A2S30S1S0S13Q40M0A1M1S14Vr;Pc8A2S12G0Vc;A2A3S1S0G1S14Vr;Pc9A2S12G0S5fVc;A1A2A3S1S0G1S14Vr;PddA2S12G0S20SaS5S32R1A1A2A1A2A3S1S0G1S14Vr;PdeA2S12G0S33R1A1A2A3S1S0G1S14Vr;PdfA2S12G0S31R1A1A2A3S1S0G1S14Vr;Pe0A2S12G0S34R1A1A2A3S1S0G1S14Vr;Pe1A2S12G0S5eS3bS36VA;A1A1Vc;A2A2A3S7S50R1S1fVn;A1M2A2S0G1S14Vr;S5cS29Ue7R2A2A1A2S12G0S2dS5S29G2R2A2S2eR3A1Z0A4A2A3F_;Fi;A2A2A2A2A2A2A2Tcs;").

Lemma qif_in : ltac2:(tb__ "0|6|
S35S5S5S5S7SeS5S5A2M0SbG0A1SbS2fA1M1G1S18SbS13Q40A1M2A1S76S5S5S0G1S39ReA1SdS2fA1A3S0S9S37RfA1SfA3S5S68R11R1A2S68VA0;R2A2F_;Fz;S71VA0;R11A2S0G1S38R12A1S8S2fS3cR11S8G0RdRcA3R10A3ScS2fRbRaA3A3A3S0S5S6fS59ReA1A1Vn;A3S0S5S20SaS5S2eS67R14S59RfA1M3A2A1A2A1S61G3A1A3S0S9S51S59R10A1M4S67R15G4A2A2Vg;A3S0S9Vvb;S72R11A1A3S69S2aS70S6eVKc;A1M5VA0;Vrho0;R17R16R14R13S8G0R12R11A3R10RfAaS7bVvb;A1ReRdRcA6S57R18R13RfRcRbA5S4S18S18S1S69S2aS70G5VA0;Vrho0;R1aR19R17R16S8G0R15R14A3R13R12AaS4eVD;A1R1R10RfA6S1S7cR1aS59R15A1R1A3S1S6S22S6R1S4bA3S2S22S6R2S44Vn;A1A3A1S0G2S14R4R3A2S14R14R3A2A3F_;F_;Fv;S1S6S5dR1S77A2S0G2S14R3R2A2S14R13R2A2A3F_;Fv;S0S43S40S2aS17R1A1A2S40S2aS17R11A1A2A3A2A2A2A2Lrho2;A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fst;Ft;Fw;Ftp;Frho;Frest;Ftmp';Fits;Fit;Fnd;Fn0;Fs;Fa;FA;").
Proof.
  intros A a s n0 nd it its tmp' rest rho tp [tr [ms md]] t st HTH HCI HQW (ESB & _) HGL Hn HFULL HGR EVB H0 QE.
  assert (EG : aa_geom A = aa_geom A0) by (unfold same_but_qcs in ESB; rewrite ESB; reflexivity).
  pose proof (K0_laws Kc HKc) as HL. set (J := JRI (K0 Kc) A0 rho0 A a n0 nd (it :: its) tmp' rest).
  pose proof (JRI_stable (K0 Kc) HL A0 rho0 A a n0 nd (it :: its) tmp' rest) as HSTB.
  pose proof (SPA_axforms segsA J _ rho _ _ tp _ (TQPs_eq vb) H0) as H1.
  destruct (proj2 H1) as (HK1 & HCB1 & HRM1 & HFRM1). cbn [w_tr w_cfg cfg_model fst snd] in HK1, HCB1, HRM1, HFRM1.
  destruct (kq_facts segsA (K0 Kc) HL A rho tp _ _ HK1) as [HG HRIG HRTC _ HST _ HCLS HQPU _ _ _ HKTOP _].
  pose proof QE as [_ _ _ _ QGEO QV _ _ _ _ _ _ _ _ _ _ _]. unfold qgeo in QGEO. destruct QGEO as (C1 & _).
  destruct QV as (_ & E200 & E201 & _).
  set (c := it_cls it) in *. set (cs := cls_of A c) in *.
  destruct (kchunks_facts c C1) as (K1 & K2 & _). rewrite Hn in K1, K2.
  pose proof (HCLS HCI c C1) as CV. fold cs in CV. pose proof (cv_ri_mu _ _ _ _ _ CV) as R48. unfold RI_mapped_user in R48.
  pose proof (qf_E A it rho t st QE) as (_ & _ & _ & Erie & _). fold c in Erie.
  pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _ & TG). unfold HIGH_SHADOW_END in S1. rewrite kSpaceSize_val in S2.
  set (SB := ag_spacebeg (aa_geom A)) in *.
  assert (RIv : region_info SB c = SB + 2 ^ 37 + 128 * c) by (unfold region_info, kRegionInfoStride; rewrite kSpaceSize_val; lia).
  set (vals := valsM n cs (region_info SB c)).
  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  set (tI := T_in n g vb (m_S0 D)).
  assert (HT : SPA segsA TJ (s_C tI) rho tp (tr, mkCfg ms md)) by (split; [exact (proj1 H1) | exact I]).

  set (dsD := [(rieQ, 48, 56, [(48, 8%nat, SVar 202)], SB + 2 ^ 37 + 128 * c)] : list dspec).
  assert (ROC : Forall (ro_cond A0 rho) dsD).
  { apply Forall_cons; [|apply Forall_nil]. apply (ro_cond_intro A0 (mkSC 0 0 0)); try reflexivity; try lia.
    - apply bv_eq. rewrite Erie, u64_lit by lia. reflexivity.
    - unfold cells_inside. repeat apply Forall_cons; try apply Forall_nil. cbn. lia.
    - intros z Hz. split; [|unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *; lia].
      left. right. right. left. exists c. split; [exact C1|]. left. rewrite <- EG. fold SB. rewrite RIv. unfold kRegionInfoStride. lia.
    - repeat apply Forall_cons; try apply Forall_nil. exists (cs_mapped_user cs). split; [cbn [eval]; pose proof QE as [_ _ _ _ _ QV' _ _ _ _ _ _ _ _ _ _ _]; exact (proj1 (proj2 (proj2 (proj2 QV'))))|].
      rewrite <- RIv. exact R48. }
  assert (HOBJ : ss_objs (ax_S (s_C tI)) = keepN (s_C tI) (s_k tI) ++ map dobj dsD) by exact (TQPs_objs vb _).
  assert (NDB : List.NoDup (map fst (combine (BSM n) vals))) by (rewrite combine_map_fst by (apply valsM_len); apply BSM_nodup; lia).
  set (rho3 := rho_absorb rho (map dobj dsD) (vms md tp ms)) in *.
  set (rho4 := rho_sets rho3 (combine (s_bs tI) vals)).
  assert (OT : forall v, ~ In v (BSM n) -> rw rho4 v = rw rho v).
  { intros v Hv. unfold rho4. rewrite rho_sets_other; [reflexivity|]. intros X0. apply Hv. unfold tI, T_in in X0. cbn [s_bs] in X0. rewrite combine_map_fst in X0 by (apply valsM_len). exact X0. }
  assert (OTlow : forall v, (v < 221)%positive -> rw rho4 v = rw rho v).
  { intros v Hv. apply OT. intros X0. destruct (BSM_range n v ltac:(lia) X0) as [[Y _]|[Y _]]; lia. }
  assert (GET : forall v x, In (v, x) (combine (BSM n) vals) -> rw rho4 v = x) by (intros v x Hin; unfold rho4, tI, T_in; cbn [s_bs]; exact (rho_sets_get _ rho3 v x NDB Hin)).
  destruct (s_step (K0 Kc) HL A0 rho0 (zbMq A it) zloQ zhiM (ZUM vb) (zsepMq A it rho t st QE vb EVB) tI J dsD vals A rho tp tr ms md
              (c_in n g vb D HC) HSTB HQW HOBJ (valsM_len n cs _) HT HK1 HFRM1 ROC) as (rho5 & H5 & V5 & RM5 & AG5 & EV5).
  { intros HK3 HF3 EV3. fold rho3 in HK3, HF3, EV3. fold rho3. fold rho4.
    assert (HK4 : K0 Kc A rho4 tp tr md).
    { apply (kq_stable segsA (K0 Kc) HL A rho3 rho4 tp tr md md); [|apply mat_equiv_refl | exact HK3]. split; [|split].
      - intros v Hv. symmetry. unfold QNPRE in Hv. apply OTlow. lia.
      - intros l0. unfold rho4. rewrite (proj1 (rho_sets_rl_rm _ rho3)). reflexivity.
      - intros x. unfold rho4. rewrite (proj2 (rho_sets_rl_rm _ rho3)). reflexivity. }
    assert (ERM4 : rm rho4 = rm rho3) by (unfold rho4; apply rm_rho_sets).
    assert (QE4 : qienvF A it rho4 t st) by (apply (qienvF_agreeV A it rho rho4 t st QE); [intros i Hi; apply OTlow; lia | rewrite ERM4; exact EV3]).
    assert (EV4 : rw rho4 200%positive = Z_to_bv 64 c /\ rw rho4 201%positive = Z_to_bv 64 (Size c)
      /\ rw rho4 221%positive = Z_to_bv 64 (Z.of_nat (length (cs_free_array cs))) /\ rw rho4 222%positive = Z_to_bv 64 (cs_mapped_free_array cs)
      /\ rw rho4 223%positive = Z_to_bv 64 (cs_allocated_user cs) /\ rw rho4 224%positive = Z_to_bv 64 (cs_mapped_user cs)
      /\ rw rho4 225%positive = Z_to_bv 64 (region_info SB c)
      /\ (forall i, (i < Z.to_nat n)%nat -> rw rho4 (Pos.of_nat (231 + i)) = Z_to_bv 64 (nth (Z.to_nat n + i) (cs_cache cs) 0))).
    { split; [rewrite OTlow by lia; exact E200|]. split; [rewrite OTlow by lia; exact E201|].
      split; [apply GET; unfold BSM, vals, valsM; cbn; tauto|]. split; [apply GET; unfold BSM, vals, valsM; cbn; tauto|]. split; [apply GET; unfold BSM, vals, valsM; cbn; tauto|].
      split; [apply GET; unfold BSM, vals, valsM; cbn; tauto|]. split; [apply GET; unfold BSM, vals, valsM; cbn; tauto|].
      intros i Hi. apply GET. exact (valsM_chunk n cs _ i Hi). }
    assert (HTOP4 : top_high A rho4) by (unfold top_high in *; rewrite !OTlow by (unfold V_DEPTH; lia); exact HKTOP).
    assert (HFpre1 : Forall (holds rho) (pre_facts DEPTH_R)).
    { pose proof (SPA_facts_hold segsA _ rho (TQPs vb) tp _ H1) as HFa. apply Forall_forall. intros f Hf.
      pose proof (proj1 (forallb_forall _ _) (TQPs_pre vb) f Hf) as X. apply existsb_exists in X as (f' & Hf' & E). apply sprop_eqb_sound in E. subst f'. exact (proj1 (Forall_forall _ _) HFa f Hf'). }
    assert (HFpre4 : Forall (holds rho4) (pre_facts DEPTH_R)).
    { apply Forall_forall. intros f0 Hf0. apply (holds_agree_vals NPRE rho rho4 f0); [| exact (proj1 (forallb_forall _ _) pre_facts_below f0 Hf0) | exact (proj1 (Forall_forall _ _) HFpre1 f0 Hf0)].
      split; [intros v Hv; symmetry; apply OTlow; unfold NPRE in *; lia | intros l0; unfold rho4; rewrite (proj1 (rho_sets_rl_rm _ rho3)); reflexivity]. }
    split; [split; [exact HK3 | split; [rewrite EV3; exact HCB1 | split; [rewrite EV3; exact HRM1 | exact HF3]]]|].
    split; [exact (carve_M Kc A rho4 tp tr md HKc HK4 HCI c n C1 Hn HFULL EV4 g HGR)|].
    split; [exact (inz_M Kc A rho4 tp tr md HKc HK4 HCI c n C1 Hn HFULL EV4 g vb _ _ _ _ _ HGR)|].
    split; [exact (in_zone_same rho4 _ _ _ _ _ (REFOBJ_K vb) (ZD_K vb) (TQPs_ref vb) (inz_K A it rho4 t st QE4 vb HTOP4 HFpre4))|].
    intros _. exact (facts_M Kc A rho4 tp tr md HKc HK4 HCI c n C1 Hn HFULL EV4 g HGR HTOP4 HFpre4). }
  exists rho5. split; [exact H5|].
  assert (VV5 : forall v, In v VSM -> rw rho5 v = rw rho4 v).
  { intros v Hv. rewrite (V5 v (SVar v)); [reflexivity|]. unfold tI, T_in. cbn [s_M]. unfold idm. apply in_map_iff. exists v. split; [reflexivity | exact Hv]. }
  assert (ERM5 : view segsA (rm rho5) = view segsA (rm rho)) by (rewrite RM5; exact EV5).
  split; [|split; [intros v Hv NB; rewrite (VV5 v Hv); exact (OT v NB) | split; [|exact ERM5]]].
  - unfold ENVM. cbv zeta. fold c cs SB.
    split; [rewrite VV5 by (unfold VSM; cbn; tauto); rewrite OTlow by lia; exact E200|]. split; [rewrite VV5 by (unfold VSM; cbn; tauto); rewrite OTlow by lia; exact E201|].
    split; [rewrite VV5 by (unfold VSM; cbn; tauto); apply GET; unfold BSM, vals, valsM; cbn; tauto|]. split; [rewrite VV5 by (unfold VSM; cbn; tauto); apply GET; unfold BSM, vals, valsM; cbn; tauto|].
    split; [rewrite VV5 by (unfold VSM; cbn; tauto); apply GET; unfold BSM, vals, valsM; cbn; tauto|]. split; [rewrite VV5 by (unfold VSM; cbn; tauto); apply GET; unfold BSM, vals, valsM; cbn; tauto|].
    split; [rewrite VV5 by (unfold VSM; cbn; tauto); apply GET; unfold BSM, vals, valsM; cbn; tauto|].
    intros i Hi. rewrite VV5; [apply GET; exact (valsM_chunk n cs _ i Hi)|].
    assert (Ei : (i <= 7)%nat) by lia. unfold VSM. do 8 (destruct i as [|i]; [first [ repeat match goal with H : _ |- _ => clear H end; cbn; tauto | cbn; tauto ] |]).     lia.
  - intros v Hv. rewrite <- (proj1 AG5 v Hv). apply OTlow. unfold NPRE in Hv. lia.
Qed.
End EntryM.
End SegQIF_glue.

