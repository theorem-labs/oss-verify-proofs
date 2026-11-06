(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cr cq cu c3.

(* [comment removed for export] *)
Module SpineMallocSecOK0E.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI"; "st0"; "W0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@Corelib.Init.Datatypes"; "list"; "false"; "prod"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "KcA"; "Kc_ok"; "Posts_malloc"; "@Corelib.Init.Logic"; "False"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS"; "ES1g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "JGsC"; "clsP"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "vm_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "E_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2"; "IMG_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I"; "nx0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IL"; "nx0"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec SpineMallocSec2 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require br.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4I.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ch.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4IL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cq.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SecRoom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SecLinks OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSecOK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.br.SpineMallocSecE0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SpineMallocSecE4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.SpineMallocSec3IE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSec4IE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineMallocSec5JE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cr.SpineMallocSec6JE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.SpineMallocSec3IEL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSec4IEL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineMallocSec5JEL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cq.SpineMallocSec6JEL.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section OK0E.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
SdSaVCST;R1A2SaS23R2A2S16F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
SdSaVCST;R1A2SaS26R2A2S16F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
SdSaVCST;R1A2S18S24R2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Hypothesis law_res : ltac2:(tb__ "0|1|
S5S3S6SbQ40A1M0A1S1fVAInv;R4R3R2R1A4S17S6S8G0G0A2A1S21S20R2A1A1S1eS0A1A3F_;Fmd;Ftp;Frho;FA;").

Theorem esec_ok_0h : ltac2:(tb__ "0|2|
S5S13S3SbQ40M0A1M1S6G1A1S14R4A1S1dS9ScG0R3A2S1bScG0S4R4PcA2A2A1A3S3SeS0S10S0S1cU0S1S27S5R1LX;R8R7R6R5A8S19S2S1Z2A3R1R4A5S11S0SfR6R4S15S12S1aS0A1VCST;VXGL;S2S1R8R7A8A5A3FrhoX;F_;F_;Ftp;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a tp HKc HC rhoX.
  exact (esec_ok_chain 0%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I.nx0 true CST XGL HCST HXGL HCSTS HCSTD (ES1g W0 st0 2)
           OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I.D2c SpineMallocSec4I.T4ac SpineMallocSec4I.T4bc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5I.C5ac OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5I.C5bc
           esec_g12_0h esec_g3_0h esec_g41_0ha esec_g41_0hb (esec_tail_0ha CST XGL HCST HXGL HCSTM HCSTS) (esec_tail_0hb CST XGL HCST HXGL HCSTM HCSTS)
           A Kc rho a tp ltac:(intros E; discriminate E) (stopJ_stable_le _) HKc HC rhoX).
Qed.

Theorem esec_ok_0l : ltac2:(tb__ "0|2|
S5S13S3SbQ40M0A1M1S6G1A1S14R4A1S1dS7ScG0R3A2S1bScG0S4R4PcA2A2A1A3S3SeS0S10S0S1cU0S1S28S5R1LX;R8R7R6R5A8S19S2S1Z2A3R1R4A5S11S0SfR6R4S15S12S1aS0A1VCST;VXGL;S2S1R8R7A8A5A3FrhoX;F_;F_;Ftp;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a tp HKc HC rhoX.
  exact (esec_ok_chain 0%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IL.nx0 false CST XGL HCST HXGL HCSTS HCSTD (ES1g W0 st0 2)
           OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IL.D2c SpineMallocSec4IL.T4ac SpineMallocSec4IL.T4bc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IL.C5ac OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IL.C5bc
           esec_g12_0l esec_g3_0l esec_g41_0la esec_g41_0lb (esec_tail_0la CST XGL HCST HXGL HCSTM HCSTS) (esec_tail_0lb CST XGL HCST HXGL HCSTM HCSTS)
           A Kc rho a tp ltac:(intros E; discriminate E) (stopJ_stable_le _) HKc HC rhoX).
Qed.

Theorem emalloc_sec_ok_0 : ltac2:(tb__ "0|0|
S5S13S3S6SbQ40A1A1S14R3A1S3SeVsegs;S10Vsegs;S25S2S1R6R5R4A5S22S2S1Z2Z8A4R1R3A5S11Vsegs;SfR4R3S15S12VAInv;VCST;VXGL;S2S1R6R5A8A5A3FrhoE;F_;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp HKc rhoE.
  eapply esec_spine with (nW := 0%nat) (st := st0) (tmax := 2) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM) (HCSTS := HCSTS) (law_res := law_res)
    (Wa := SWa_0) (Da := SDa_0) (Wb := SWb_0) (FB := SFB) (NXS0 := NXS0_0) (ECertS1 := ECertS1_0) (WC1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.WC1_0) (DC1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.DC1_0)
    (NXC1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.NXC1_0) (IC1 := IC1_0) (R17 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.R17_0) (R11 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.R11_0) (R12 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.R12_0) (R13 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.R13_0)
    (R14 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.R14_0) (R15 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.R15_0) (NX1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.NX1_0) (NXS1f := NXS1f_0) (ECertSf := ECertSf_0) (FC1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.FC1_0)
    (RN := RN_0) (WRn := WRn_0) (DKRn := DKRn_0) (NXRn := NXRn_0) (ENTn := ENTn_0) (IDn := IDn_0)
    (R10 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.R10_0) (XC1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.XC1_0) (SK1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.SK1_0)
    (Jo := fun a => OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.JGsC 0%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I.nx0 (fun X : AA => X) A Kc rho a).
  - intros E. discriminate E.
  - exact (stopJ_stable_le _).
  - exact HKc.
  - unfold Posts_malloc. left. reflexivity.
  - intros rhoX tr ms md a Hsp HJG Hpl. pose proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.NX1_0 as NX1'. unfold W0, st0 in NX1'. unfold W0, st0 in *. rewrite NX1'.
    exact (grant_Jo 0%nat st0 2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I.nx0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I.Hnx_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I.NXG_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.R11_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.FC1_0 A Kc rho rhoX tp tr ms md a (stopJ_stable_le _) HKc Hsp HJG Hpl).
  - intros rhoX a. unfold W0, st0 in *. rewrite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I.Hnx_0.
    apply (ecls_split 0%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I.nx0 A Kc rho a (ES1g W0 st0 2) _ tp).
    + intros HC. exact (esec_ok_0h A Kc rho a tp HKc HC _).
    + intros HC. exact (esec_ok_0l A Kc rho a tp HKc HC _).
Qed.
End OK0E.
End SpineMallocSecOK0E.

(* [comment removed for export] *)
Module SpineMallocSecOK0EW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2"; "st0"; "W0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@Corelib.Init.Datatypes"; "list"; "false"; "prod"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "KcA"; "Kc_ok"; "Posts_malloc"; "@Corelib.Init.Logic"; "False"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS"; "ES1g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "JGsC"; "clsP"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "vm_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "E_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2"; "IMG_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3ILW2"; "nx0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2"; "nx0"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec SpineMallocSec2 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require br.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4IW2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require co.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4ILW2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cr.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SecRoom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SecLinks OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSecOK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.br.SpineMallocSecE0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SpineMallocSecE4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec3IEW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.SpineMallocSec4IEW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.co.SpineMallocSec5JEW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cu.SpineMallocSec6JEW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.SpineMallocSec3IELW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSec4IELW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.co.SpineMallocSec5JELW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cr.SpineMallocSec6JELW2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section OK0E.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
SdSaVCST;R1A2SaS23R2A2S16F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
SdSaVCST;R1A2SaS26R2A2S16F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
SdSaVCST;R1A2S18S24R2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Hypothesis law_res : ltac2:(tb__ "0|1|
S5S3S6SbQ40A1M0A1S1fVAInv;R4R3R2R1A4S17S6S8G0G0A2A1S21S20R2A1A1S1eS0A1A3F_;Fmd;Ftp;Frho;FA;").

Theorem esec_ok_2h : ltac2:(tb__ "0|2|
S5S13S3SbQ40M0A1M1S6G1A1S14R4A1S1dS9ScG0R3A2S1bScG0S4R4PcA2A2A1A3S3SeS0S10S0S1cU2S1S28S5R1LX;R8R7R6R5A8S19S2S1Z4A3R1R4A5S11S0SfR6R4S15S12S1aS0A1VCST;VXGL;S2S1R8R7A8A5A3FrhoX;F_;F_;Ftp;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a tp HKc HC rhoX.
  exact (esec_ok_chain 2%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.nx0 true CST XGL HCST HXGL HCSTS HCSTD (ES1g W0 st0 4)
           OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.D2c SpineMallocSec4IW2.T4ac SpineMallocSec4IW2.T4bc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IW2.C5ac OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IW2.C5bc
           esec_g12_2h esec_g3_2h esec_g41_2ha esec_g41_2hb (esec_tail_2ha CST XGL HCST HXGL HCSTM HCSTS) (esec_tail_2hb CST XGL HCST HXGL HCSTM HCSTS)
           A Kc rho a tp ltac:(intros E; discriminate E) (stopJ_stable_le _) HKc HC rhoX).
Qed.

Theorem esec_ok_2l : ltac2:(tb__ "0|2|
S5S13S3SbQ40M0A1M1S6G1A1S14R4A1S1dS7ScG0R3A2S1bScG0S4R4PcA2A2A1A3S3SeS0S10S0S1cU2S1S27S5R1LX;R8R7R6R5A8S19S2S1Z4A3R1R4A5S11S0SfR6R4S15S12S1aS0A1VCST;VXGL;S2S1R8R7A8A5A3FrhoX;F_;F_;Ftp;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a tp HKc HC rhoX.
  exact (esec_ok_chain 2%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3ILW2.nx0 false CST XGL HCST HXGL HCSTS HCSTD (ES1g W0 st0 4)
           OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3ILW2.D2c SpineMallocSec4ILW2.T4ac SpineMallocSec4ILW2.T4bc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5ILW2.C5ac OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5ILW2.C5bc
           esec_g12_2l esec_g3_2l esec_g41_2la esec_g41_2lb (esec_tail_2la CST XGL HCST HXGL HCSTM HCSTS) (esec_tail_2lb CST XGL HCST HXGL HCSTM HCSTS)
           A Kc rho a tp ltac:(intros E; discriminate E) (stopJ_stable_le _) HKc HC rhoX).
Qed.

Theorem emalloc_sec_ok_2 : ltac2:(tb__ "0|0|
S5S13S3S6SbQ40A1A1S14R3A1S3SeVsegs;S10Vsegs;S25S2S1R6R5R4A5S22S2S1Z4Z8A4R1R3A5S11Vsegs;SfR4R3S15S12VAInv;VCST;VXGL;S2S1R6R5A8A5A3FrhoE;F_;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp HKc rhoE.
  eapply esec_spine with (nW := 2%nat) (st := st0) (tmax := 4) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM) (HCSTS := HCSTS) (law_res := law_res)
    (Wa := SWa_0) (Da := SDa_0) (Wb := SWb_0) (FB := SFB) (NXS0 := NXS0_0) (ECertS1 := ECertS1_0) (WC1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.WC1_0) (DC1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.DC1_0)
    (NXC1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.NXC1_0) (IC1 := IC1_0) (R17 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.R17_0) (R11 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.R11_0) (R12 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.R12_0) (R13 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.R13_0)
    (R14 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.R14_0) (R15 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.R15_0) (NX1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.NX1_0) (NXS1f := NXS1f_0) (ECertSf := ECertSf_0) (FC1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.FC1_0)
    (RN := RN_0) (WRn := WRn_0) (DKRn := DKRn_0) (NXRn := NXRn_0) (ENTn := ENTn_0) (IDn := IDn_0)
    (R10 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.R10_0) (XC1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.XC1_0) (SK1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.SK1_0)
    (Jo := fun a => OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.JGsC 2%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.nx0 (fun X : AA => X) A Kc rho a).
  - intros E. discriminate E.
  - exact (stopJ_stable_le _).
  - exact HKc.
  - unfold Posts_malloc. left. reflexivity.
  - intros rhoX tr ms md a Hsp HJG Hpl. pose proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.NX1_0 as NX1'. unfold W0, st0 in NX1'. unfold W0, st0 in *. rewrite NX1'.
    exact (grant_Jo 2%nat st0 4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.nx0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.Hnx_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.NXG_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.R11_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.FC1_0 A Kc rho rhoX tp tr ms md a (stopJ_stable_le _) HKc Hsp HJG Hpl).
  - intros rhoX a. unfold W0, st0 in *. rewrite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.Hnx_0.
    apply (ecls_split 2%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.nx0 A Kc rho a (ES1g W0 st0 4) _ tp).
    + intros HC. exact (esec_ok_2h A Kc rho a tp HKc HC _).
    + intros HC. exact (esec_ok_2l A Kc rho a tp HKc HC _).
Qed.
End OK0E.
End SpineMallocSecOK0EW2.

(* [comment removed for export] *)
Module SpineMallocSecOK0SEW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2"; "st0"; "W0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "AE_A"; "JL_malloc_ok"; "L_malloc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "prod"; "false"; "pair"; "true"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@Corelib.Init.Logic"; "False"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS"; "ES1g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "JGsC"; "clsP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "E_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.IfaceS"; "alloc_roomA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2"; "IMG_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3ILW2"; "nx0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2"; "nx0"; "@Stdlib.Lists.List"; "In"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec SpineMallocSec2 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require br.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4IW2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require co.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4ILW2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cr.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SecRoom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SecLinks OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSecOK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.br.SpineMallocSecE0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SpineMallocSecE4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec3IEW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.SpineMallocSec4IEW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.co.SpineMallocSec5JEW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cu.SpineMallocSec6JEW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.SpineMallocSec3IELW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSec4IELW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.co.SpineMallocSec5JELW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cr.SpineMallocSec6JELW2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require IfaceS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require br.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.IfaceS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.br.SpineMallocSec2S OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSecOKP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.SpineMallocSecE4P.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section OK0E.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S13SbVCST;R1A2SbS23R2A2S1aF_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S13SbVCST;R1A2SbS26R2A2S1aF_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S13SbVCST;R1A2S1bS24R2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Variable PF : ltac2:(tb__ "0|0|
S1S6SeSfS17S19A2A1F_;F_;").
Hypothesis HPF : ltac2:(tb__ "0|0|
S1S6S29SfS17S19A2S11S17S19SaS8S3S2A3S9S22S0A1VCST;VXGL;R2R1A5A4VPF;R2R1A2A3FKc;FA;").

Theorem esec_ok_2h_S : ltac2:(tb__ "0|2|
S1S6S4SdQ40M0A1M1SeG1A1S7R4A1S1fS12ScG0R3A2S1dScG0S5R4PcA2A2A1A3S4S14S0S16S0S1eU2S2S28S1R1LX;R8R7R6R5A8S1cS3S2Z4A3R1R4A5S18S0S15R6R4VPF;R8R7A2A5A3FrhoX;F_;F_;Ftp;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a tp HKc HC rhoX.
  exact (esec_ok_chain_P 2%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.nx0 true CST XGL HCST HXGL HCSTS HCSTD PF (ES1g W0 st0 4)
           OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.D2c SpineMallocSec4IW2.T4ac SpineMallocSec4IW2.T4bc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IW2.C5ac OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IW2.C5bc
           esec_g12_2h esec_g3_2h esec_g41_2ha esec_g41_2hb (fun A' Kc' rho0' rho' a' tp0' G2' => esec_tail_2ha_P CST XGL HCST HXGL HCSTM HCSTS A' Kc' rho0' rho' a' tp0' G2' (PF A' Kc') (HPF A' Kc')) (fun A' Kc' rho0' rho' a' tp0' G2' => esec_tail_2hb_P CST XGL HCST HXGL HCSTM HCSTS A' Kc' rho0' rho' a' tp0' G2' (PF A' Kc') (HPF A' Kc'))
           A Kc rho a tp ltac:(intros E; discriminate E) (stopJ_stable_le _) HKc HC rhoX).
Qed.

Theorem esec_ok_2l_S : ltac2:(tb__ "0|2|
S1S6S4SdQ40M0A1M1SeG1A1S7R4A1S1fS10ScG0R3A2S1dScG0S5R4PcA2A2A1A3S4S14S0S16S0S1eU2S2S27S1R1LX;R8R7R6R5A8S1cS3S2Z4A3R1R4A5S18S0S15R6R4VPF;R8R7A2A5A3FrhoX;F_;F_;Ftp;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a tp HKc HC rhoX.
  exact (esec_ok_chain_P 2%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3ILW2.nx0 false CST XGL HCST HXGL HCSTS HCSTD PF (ES1g W0 st0 4)
           OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3ILW2.D2c SpineMallocSec4ILW2.T4ac SpineMallocSec4ILW2.T4bc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5ILW2.C5ac OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5ILW2.C5bc
           esec_g12_2l esec_g3_2l esec_g41_2la esec_g41_2lb (fun A' Kc' rho0' rho' a' tp0' G2' => esec_tail_2la_P CST XGL HCST HXGL HCSTM HCSTS A' Kc' rho0' rho' a' tp0' G2' (PF A' Kc') (HPF A' Kc')) (fun A' Kc' rho0' rho' a' tp0' G2' => esec_tail_2lb_P CST XGL HCST HXGL HCSTM HCSTS A' Kc' rho0' rho' a' tp0' G2' (PF A' Kc') (HPF A' Kc'))
           A Kc rho a tp ltac:(intros E; discriminate E) (stopJ_stable_le _) HKc HC rhoX).
Qed.

Theorem emalloc_sec_ok_2_S : ltac2:(tb__ "0|1|
S1S6S4SeSdQ40M0A1A1S7R3A1S21R5ScG0S5R3PcA2A2A2S4S14Vsegs;S16Vsegs;S25S3S2R7R6R5A5S20S3S2Z4Z8A4R1R4A5S18Vsegs;S15R5R4VPF;R7R6A2A5A3FrhoE;F_;F_;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp HKc HROOM rhoE.
  eapply esec_spine_S with (nW := 2%nat) (st := st0) (tmax := 4)
    (Wa := SWa_0) (Da := SDa_0) (Wb := SWb_0) (FB := SFB) (NXS0 := NXS0_0) (ECertS1 := ECertS1_0) (WC1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.WC1_0) (DC1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.DC1_0)
    (NXC1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.NXC1_0) (IC1 := IC1_0) (R17 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.R17_0) (R11 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.R11_0) (R12 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.R12_0) (R13 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.R13_0)
    (R14 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.R14_0) (R15 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.R15_0) (NX1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.NX1_0)  (FC1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.FC1_0)

    (R10 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.R10_0) (XC1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.XC1_0) (SK1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.SK1_0)
    (Jo := fun a => OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.JGsC 2%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.nx0 (fun X : AA => X) A Kc rho a).
  - intros E. discriminate E.
  - exact (stopJ_stable_le _).
  - exact HKc.
  - exact HROOM.
  - intros rhoX tr ms md a Hsp HJG Hpl. pose proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.NX1_0 as NX1'. unfold W0, st0 in NX1'. unfold W0, st0 in *. rewrite NX1'.
    exact (grant_Jo 2%nat st0 4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.nx0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.Hnx_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.NXG_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.R11_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.FC1_0 A Kc rho rhoX tp tr ms md a (stopJ_stable_le _) HKc Hsp HJG Hpl).
  - intros rhoX a. unfold W0, st0 in *. rewrite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.Hnx_0.
    apply (ecls_split 2%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.nx0 A Kc rho a (ES1g W0 st0 4) _ tp).
    + intros HC. exact (esec_ok_2h_S A Kc rho a tp HKc HC _).
    + intros HC. exact (esec_ok_2l_S A Kc rho a tp HKc HC _).
Qed.
End OK0E.
End SpineMallocSecOK0SEW2.

(* [comment removed for export] *)
Module SpineCallocSec6JL.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "list"; "prod"; "length"; "pair"; "None"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "sobj"; "rl"; "sv"; "holds"; "sprop"; "SVar"; "eval"; "obj_range"; "SAlu"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "DG"; "aa_sec"; "sec_chunk"; "aa_Km"; "aa_ptr_committed"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "div"; "of_nat"; "lt"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS"; "AXK"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "JGs"; "range_noband"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IL"; "nx0"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump"; "bumpP"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv"; "bumpV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "JLc_ok"; "Lc_ok"; "PFc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "V_NRES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineCallocSec5IL"; "C5ac"; "C5bc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cu.SpineCallocSec6IL"; "FXPa"; "FXPb"; "PXa"; "PXb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec7"; "bx_ok"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2"; "IMG_S"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec4IL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ch.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec4IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CertCallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cc.SpineCallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec6L OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineCallocSec5IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cu.SpineCallocSec6IL.
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

Theorem sec_tail_0la_P : ltac2:(tb__ "0|9|
S37OF_;S15S2aS8S8S27Q40M0A1M1S0G1A1M2S16S0S1S3cS3eA2M3A1S32G3S3S3cS3eS48VW;Vst;A2S47VCST;VXGL;R8R7A4A4R1A3S45VW;Vst;A2S2bR9A1S3bS1fRcS3aRaA1A3S7S1bG1S9RaR1A2S9RbR1A2A3Fi;S7S1bS0S27Q8A1M4A1ScRbR1A2ScRcR1A2A3Fl;S2cVCST;VXGL;ReReSaRcA1SaRbA1A6S20S23S2S18S17RfA1A2A1S19RfA1A2S1S6S6A2M5S32G5R1S42RbA1A3S40R2S3S6S6S28G0ReA2M6S44S28G0S9RfPcA2A2A1M7A4A2F_;Fbn;S6S1cS20S3fG6A1M8R1A2S24R1S21G8S22G7Z8A2A2A2A2S1dS1bS5G4A1SaR10S29G0R2A2A2S4G4A1A3A1F_;Fz;S8G2S36S1fR15S39S1fS2dU0Vst;S2fS26S15S33R1A1LX;ReA2R14R13R11R10A8S4bR2R1A5S3dS1fS38R12RfRdA5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 G2 Posts HPin HUS HKc Hokl HLw HLl HKEPT HL9 HDB RUNDEF.
  set (BX := AXK (fun X : AA => bumpP X) G2). set (Q := LQPA segsA NF rho0 tp0 Posts).
  assert (HW : stopJ_w W st) by (hw_discharge).
  assert (BXg : forall X, aa_geom (BX X) = aa_geom X) by (intros X; reflexivity).
  apply (sec_g43_low 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXa FXPa (PXnba_0 G2) C5ac C5Aa Y6Aa E6a CT6a CO6a T6a s6Aa s6a R6a
           FLOWa_0 HC5Aa_0 FBAa_0 Cert6Aa_0 E6Aa_0 I6Aa_0
           WC6a_0 DF6a_0 NX6a_0 HC6a_0 SK6a_0 FC6a_0 FX6a_0 XC6a_0 HCO6a_0 WCO6a_0 He6a_0 Hchk6a_0 HT6a_0 FBC6a_0 FBT6a_0 NXC6a_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY6 tY6. rewrite HD6a_0.
  revert rY6 tY6. apply (hint_low_triple 0%nat st nx0 BX D6a D6La (F_g7L nx0) WD6La_0 DD6La_0 NXD6La_0 HD6La_0 FLOW6a_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g7L_hold 0%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) ok A Kc rho a Q). intros rY6 tY6.
  apply (sec_g44 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXa FXPa (PXnba_0 G2) D6La U7a ET7a CT7a CO7a CR7a CS7a CM7a T7a s7a R7a n7a
           WU7a_0 DU7a_0 NXU7a_0 HU7a_0 Cert7a_0 WC7a_0 DF7a_0 NX7a_0 HC7a_0 SK7a_0 FC7a_0 FX7a_0 XC7a_0 HCO7a_0 WCO7a_0
           RB7a_0 HCR7a_0 LEN7a_0 PERM_nd7a_0 PERM_lt7a_0 PERM_cov7a_0 HCS7a_0 MRG7a_0 HCM7a_0 He7a_0 Hchk7a_0 HT7a_0 FBC7a_0 FBT7a_0 NXC7a_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY7 tY7. rewrite HD7a_0.
  revert rY7 tY7. apply (hint_low_triple 0%nat st nx0 BX D7a D7La (F_g8L nx0) WD7La_0 DD7La_0 NXD7La_0 HD7La_0 FLOW7a_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g8L_hold 0%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) ok A Kc rho a Q). intros rY7 tY7.
  apply (sec_g45 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXa FXPa (PXnba_0 G2) D7La U8a ET8a CT8a CO8a T8a s8a R8a
           WU8a_0 DU8a_0 NXU8a_0 HU8a_0 Cert8a_0 WC8a_0 DF8a_0 NX8a_0 HC8a_0 SK8a_0 FC8a_0 FX8a_0 XC8a_0 HCO8a_0 WCO8a_0
           He8a_0 Hchk8a_0 HT8a_0 FBC8a_0 FBT8a_0 NXC8a_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY8 tY8. rewrite HD8a_0.
  revert rY8 tY8. apply (hint_low_triple 0%nat st nx0 BX D8a D8La (F_g9L nx0) WD8La_0 DD8La_0 NXD8La_0 HD8La_0 FLOW8a_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g9L_hold 0%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) ok A Kc rho a Q). intros rY8 tY8.
  apply (sec_g46 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXa FXPa (PXnba_0 G2) D8La U9a E9fa E9pa CO9pa E9qa
           WU9a_0 DU9a_0 NXU9a_0 HU9a_0 Cert9a_0 SK9a_0 FC9a_0 FX9a_0 FP9a_0 XC9a_0 HCO9a_0 WCO9a_0 Cert9qa_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  - intros rY9 tY9.
    apply (sec_g47 0%nat st nx0 BX E9fa S9afa S9bfa D9fa iMfa perm9fa HS9afa_0 HS9bfa_0 HD9fa_0 NDpfa_0 BNDpfa_0 COVpfa_0 ok A Kc rho a Q).
    intros rZ tZ.
    exact (sec_g48_P 0%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXoka_0 G2) 131072 DZero (SAlu ALU_ADD (SVar V_NRES) (SLit 16384)) FXPa ltac:(first [left; reflexivity | right; reflexivity]) (HPATHa_0 G2)
             false FFfa swcfa c1fa c2fa c4fa c5fa mcfa xcfa tybfa SELFfa_0 NDFfa_0 BNDFfa_0 COVFfa_0 XFnfa_0 BFbfa_0 FPFfa_0 FXFfa_0 FPARfa_0
             Hc1fa_0 Hmcfa_0 Htybfa_0 Hxcfa_0 WCUfa_0 SELUfa_0 NDUfa_0 BNDUfa_0 COVUfa_0 W9fa_0 D9fa_0 XB9fa_0 sFfa ENT9fa_0 SID9fa_0 G110fa_0 D9fa CertFfa_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
  - intros rY9 tY9.
    apply (sec_g47 0%nat st nx0 BX E9qa S9aqa S9bqa D9qa iMqa perm9qa HS9aqa_0 HS9bqa_0 HD9qa_0 NDpqa_0 BNDpqa_0 COVpqa_0 ok A Kc rho a Q).
    intros rZ tZ.
    exact (sec_g48_P 0%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXoka_0 G2) 131072 DZero (SAlu ALU_ADD (SVar V_NRES) (SLit 16384)) FXPa ltac:(first [left; reflexivity | right; reflexivity]) (HPATHa_0 G2)
             true FFqa swcqa c1qa c2qa c4qa c5qa mcqa xcqa tybqa SELFqa_0 NDFqa_0 BNDFqa_0 COVFqa_0 XFnqa_0 BFbqa_0 FPFqa_0 FXFqa_0 FPARqa_0
             Hc1qa_0 Hmcqa_0 Htybqa_0 Hxcqa_0 WCUqa_0 SELUqa_0 NDUqa_0 BNDUqa_0 COVUqa_0 W9qa_0 D9qa_0 XB9qa_0 sFqa ENT9qa_0 SID9qa_0 G110qa_0 D9qa CertFqa_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
Qed.

Theorem sec_tail_0la : ltac2:(tb__ "0|8|
S37OF_;S15S2aS8S8S27Q40M0A1M1S0G1A1M2S16S45VW;Vst;A2S2bR7A1S3bS1fRaS3aR8A1A3S7S1bG1S9R8R1A2S9R9R1A2A3Fi;S7S1bS0S27Q8A1M3A1ScR9R1A2ScRaR1A2A3Fl;S2cVCST;VXGL;RcRcSaRaA1SaR9A1A6S20S23S2S18S17RdA1A2A1S19RdA1A2S1S6S6A2M4S32G4R1S42R9A1A3S40R2S3S6S6S28G0RcA2M5S44S28G0S9RdPcA2A2A1M6A4A2F_;Fbn;S6S1cS20S3fG5A1M7R1A2S24R1S21G7S22G6Z8A2A2A2A2S1dS1bS5G3A1SaReS29G0R2A2A2S4G3A1A3A1F_;Fz;S8G2S36S1fR13S39S1fS2dU0Vst;S2fS26S15S33R1A1LX;RcA2R12R11RfReA8S4bR2R1A5S3dS1fS38R10RdS49VCST;VXGL;VW;Vst;R12R11A6A5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 G2. exact (sec_tail_0la_P ok A Kc rho0 rho a tp0 G2 (PFc CST XGL W st A Kc) (or_intror (or_introl eq_refl))).
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

Theorem sec_tail_0lb_P : ltac2:(tb__ "0|9|
S37OF_;S15S2aS8S8S27Q40M0A1M1S0G1A1M2S16S0S1S3cS3eA2M3A1S32G3S3S3cS3eS48VW;Vst;A2S47VCST;VXGL;R8R7A4A4R1A3S45VW;Vst;A2S2bR9A1S3bS1fRcS3aRaA1A3S7S1bG1S9RaR1A2S9RbR1A2A3Fi;S7S1bS0S27Q8A1M4A1ScRbR1A2ScRcR1A2A3Fl;S2cVCST;VXGL;ReReSaRcA1SaRbA1A6S20S23S2S18S17RfA1A2A1S19RfA1A2S1S6S6A2M5S32G5R1S42RbA1A3S40R2S3S6S6S28G0ReA2M6S44S28G0S9RfPcA2A2A1M7A4A2F_;Fbn;S6S1cS20S3fG6A1M8R1A2S24R1S21G8S22G7Z8A2A2A2A2S1dS1bS5G4A1SaR10S29G0R2A2A2S4G4A1A3A1F_;Fz;S8G2S36S1fR15S39S1fS2dU0Vst;S2fS26S15R1LX;ReA2R14R13R11R10A8S4cR2R1A5S3dS1fS38R12RfRdA5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 G2 Posts HPin HUS HKc Hokl HLw HLl HKEPT HL9 HDB RUNDEF.
  set (BX := AXK (fun X : AA => X) G2). set (Q := LQPA segsA NF rho0 tp0 Posts).
  assert (HW : stopJ_w W st) by (hw_discharge).
  assert (BXg : forall X, aa_geom (BX X) = aa_geom X) by (intros X; reflexivity).
  apply (sec_g43_low 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXb FXPb (PXnbb_0 G2) C5bc C5Ab Y6Ab E6b CT6b CO6b T6b s6Ab s6b R6b
           FLOWb_0 HC5Ab_0 FBAb_0 Cert6Ab_0 E6Ab_0 I6Ab_0
           WC6b_0 DF6b_0 NX6b_0 HC6b_0 SK6b_0 FC6b_0 FX6b_0 XC6b_0 HCO6b_0 WCO6b_0 He6b_0 Hchk6b_0 HT6b_0 FBC6b_0 FBT6b_0 NXC6b_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY6 tY6. rewrite HD6b_0.
  revert rY6 tY6. apply (hint_low_triple 0%nat st nx0 BX D6b D6Lb (F_g7L nx0) WD6Lb_0 DD6Lb_0 NXD6Lb_0 HD6Lb_0 FLOW6b_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g7L_hold 0%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) ok A Kc rho a Q). intros rY6 tY6.
  apply (sec_g44 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXb FXPb (PXnbb_0 G2) D6Lb U7b ET7b CT7b CO7b CR7b CS7b CM7b T7b s7b R7b n7b
           WU7b_0 DU7b_0 NXU7b_0 HU7b_0 Cert7b_0 WC7b_0 DF7b_0 NX7b_0 HC7b_0 SK7b_0 FC7b_0 FX7b_0 XC7b_0 HCO7b_0 WCO7b_0
           RB7b_0 HCR7b_0 LEN7b_0 PERM_nd7b_0 PERM_lt7b_0 PERM_cov7b_0 HCS7b_0 MRG7b_0 HCM7b_0 He7b_0 Hchk7b_0 HT7b_0 FBC7b_0 FBT7b_0 NXC7b_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY7 tY7. rewrite HD7b_0.
  revert rY7 tY7. apply (hint_low_triple 0%nat st nx0 BX D7b D7Lb (F_g8L nx0) WD7Lb_0 DD7Lb_0 NXD7Lb_0 HD7Lb_0 FLOW7b_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g8L_hold 0%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) ok A Kc rho a Q). intros rY7 tY7.
  apply (sec_g45 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXb FXPb (PXnbb_0 G2) D7Lb U8b ET8b CT8b CO8b T8b s8b R8b
           WU8b_0 DU8b_0 NXU8b_0 HU8b_0 Cert8b_0 WC8b_0 DF8b_0 NX8b_0 HC8b_0 SK8b_0 FC8b_0 FX8b_0 XC8b_0 HCO8b_0 WCO8b_0
           He8b_0 Hchk8b_0 HT8b_0 FBC8b_0 FBT8b_0 NXC8b_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY8 tY8. rewrite HD8b_0.
  revert rY8 tY8. apply (hint_low_triple 0%nat st nx0 BX D8b D8Lb (F_g9L nx0) WD8Lb_0 DD8Lb_0 NXD8Lb_0 HD8Lb_0 FLOW8b_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g9L_hold 0%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) ok A Kc rho a Q). intros rY8 tY8.
  apply (sec_g46 0%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXb FXPb (PXnbb_0 G2) D8Lb U9b E9fb E9pb CO9pb E9qb
           WU9b_0 DU9b_0 NXU9b_0 HU9b_0 Cert9b_0 SK9b_0 FC9b_0 FX9b_0 FP9b_0 XC9b_0 HCO9b_0 WCO9b_0 Cert9qb_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  - intros rY9 tY9.
    apply (sec_g47 0%nat st nx0 BX E9fb S9afb S9bfb D9fb iMfb perm9fb HS9afb_0 HS9bfb_0 HD9fb_0 NDpfb_0 BNDpfb_0 COVpfb_0 ok A Kc rho a Q).
    intros rZ tZ.
    exact (sec_g48_P 0%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXokb_0 G2) 8 DUnknown (SVar V_NRES) FXPb ltac:(first [left; reflexivity | right; reflexivity]) (HPATHb_0 G2)
             false FFfb swcfb c1fb c2fb c4fb c5fb mcfb xcfb tybfb SELFfb_0 NDFfb_0 BNDFfb_0 COVFfb_0 XFnfb_0 BFbfb_0 FPFfb_0 FXFfb_0 FPARfb_0
             Hc1fb_0 Hmcfb_0 Htybfb_0 Hxcfb_0 WCUfb_0 SELUfb_0 NDUfb_0 BNDUfb_0 COVUfb_0 W9fb_0 D9fb_0 XB9fb_0 sFfb ENT9fb_0 SID9fb_0 G110fb_0 D9fb CertFfb_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
  - intros rY9 tY9.
    apply (sec_g47 0%nat st nx0 BX E9qb S9aqb S9bqb D9qb iMqb perm9qb HS9aqb_0 HS9bqb_0 HD9qb_0 NDpqb_0 BNDpqb_0 COVpqb_0 ok A Kc rho a Q).
    intros rZ tZ.
    exact (sec_g48_P 0%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXokb_0 G2) 8 DUnknown (SVar V_NRES) FXPb ltac:(first [left; reflexivity | right; reflexivity]) (HPATHb_0 G2)
             true FFqb swcqb c1qb c2qb c4qb c5qb mcqb xcqb tybqb SELFqb_0 NDFqb_0 BNDFqb_0 COVFqb_0 XFnqb_0 BFbqb_0 FPFqb_0 FXFqb_0 FPARqb_0
             Hc1qb_0 Hmcqb_0 Htybqb_0 Hxcqb_0 WCUqb_0 SELUqb_0 NDUqb_0 BNDUqb_0 COVUqb_0 W9qb_0 D9qb_0 XB9qb_0 sFqb ENT9qb_0 SID9qb_0 G110qb_0 D9qb CertFqb_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
Qed.

Theorem sec_tail_0lb : ltac2:(tb__ "0|8|
S37OF_;S15S2aS8S8S27Q40M0A1M1S0G1A1M2S16S45VW;Vst;A2S2bR7A1S3bS1fRaS3aR8A1A3S7S1bG1S9R8R1A2S9R9R1A2A3Fi;S7S1bS0S27Q8A1M3A1ScR9R1A2ScRaR1A2A3Fl;S2cVCST;VXGL;RcRcSaRaA1SaR9A1A6S20S23S2S18S17RdA1A2A1S19RdA1A2S1S6S6A2M4S32G4R1S42R9A1A3S40R2S3S6S6S28G0RcA2M5S44S28G0S9RdPcA2A2A1M6A4A2F_;Fbn;S6S1cS20S3fG5A1M7R1A2S24R1S21G7S22G6Z8A2A2A2A2S1dS1bS5G3A1SaReS29G0R2A2A2S4G3A1A3A1F_;Fz;S8G2S36S1fR13S39S1fS2dU0Vst;S2fS26S15R1LX;RcA2R12R11RfReA8S4cR2R1A5S3dS1fS38R10RdS49VCST;VXGL;VW;Vst;R12R11A6A5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 G2. exact (sec_tail_0lb_P ok A Kc rho0 rho a tp0 G2 (PFc CST XGL W st A Kc) (or_intror (or_introl eq_refl))).
Qed.
End INST.
End SpineCallocSec6JL.

(* [comment removed for export] *)
Module SpineCallocSec6JLW1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "list"; "prod"; "length"; "pair"; "None"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "sobj"; "rl"; "sv"; "holds"; "sprop"; "SVar"; "eval"; "obj_range"; "SAlu"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "DG"; "aa_sec"; "sec_chunk"; "aa_Km"; "aa_ptr_committed"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "div"; "of_nat"; "lt"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS"; "AXK"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "JGs"; "range_noband"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3ILW1"; "nx0"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump"; "bumpP"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv"; "bumpV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "JLc_ok"; "Lc_ok"; "PFc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "V_NRES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.co.SpineCallocSec5ILW1"; "C5ac"; "C5bc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cu.SpineCallocSec6ILW1"; "FXPa"; "FXPb"; "PXa"; "PXb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec7"; "bx_ok"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2"; "IMG_S"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec4ILW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ch.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require co.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3ILW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec4ILW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CertCallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cc.SpineCallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec6L OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.co.SpineCallocSec5ILW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cu.SpineCallocSec6ILW1.
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

Theorem sec_tail_0la_P : ltac2:(tb__ "0|9|
S37OF_;S15S2aS8S8S27Q40M0A1M1S0G1A1M2S16S0S1S3cS3eA2M3A1S32G3S3S3cS3eS48VW;Vst;A2S47VCST;VXGL;R8R7A4A4R1A3S45VW;Vst;A2S2bR9A1S3bS1fRcS3aRaA1A3S7S1bG1S9RaR1A2S9RbR1A2A3Fi;S7S1bS0S27Q8A1M4A1ScRbR1A2ScRcR1A2A3Fl;S2cVCST;VXGL;ReReSaRcA1SaRbA1A6S20S23S2S18S17RfA1A2A1S19RfA1A2S1S6S6A2M5S32G5R1S42RbA1A3S40R2S3S6S6S28G0ReA2M6S44S28G0S9RfPcA2A2A1M7A4A2F_;Fbn;S6S1cS20S3fG6A1M8R1A2S24R1S21G8S22G7Z8A2A2A2A2S1dS1bS5G4A1SaR10S29G0R2A2A2S4G4A1A3A1F_;Fz;S8G2S36S1fR15S39S1fS2dU1Vst;S2fS26S15S33R1A1LX;ReA2R14R13R11R10A8S4bR2R1A5S3dS1fS38R12RfRdA5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 G2 Posts HPin HUS HKc Hokl HLw HLl HKEPT HL9 HDB RUNDEF.
  set (BX := AXK (fun X : AA => bumpP X) G2). set (Q := LQPA segsA NF rho0 tp0 Posts).
  assert (HW : stopJ_w W st) by (hw_discharge).
  assert (BXg : forall X, aa_geom (BX X) = aa_geom X) by (intros X; reflexivity).
  apply (sec_g43_low 1%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXa FXPa (PXnba_0 G2) C5ac C5Aa Y6Aa E6a CT6a CO6a T6a s6Aa s6a R6a
           FLOWa_0 HC5Aa_0 FBAa_0 Cert6Aa_0 E6Aa_0 I6Aa_0
           WC6a_0 DF6a_0 NX6a_0 HC6a_0 SK6a_0 FC6a_0 FX6a_0 XC6a_0 HCO6a_0 WCO6a_0 He6a_0 Hchk6a_0 HT6a_0 FBC6a_0 FBT6a_0 NXC6a_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY6 tY6. rewrite HD6a_0.
  revert rY6 tY6. apply (hint_low_triple 1%nat st nx0 BX D6a D6La (F_g7L nx0) WD6La_0 DD6La_0 NXD6La_0 HD6La_0 FLOW6a_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g7L_hold 1%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) ok A Kc rho a Q). intros rY6 tY6.
  apply (sec_g44 1%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXa FXPa (PXnba_0 G2) D6La U7a ET7a CT7a CO7a CR7a CS7a CM7a T7a s7a R7a n7a
           WU7a_0 DU7a_0 NXU7a_0 HU7a_0 Cert7a_0 WC7a_0 DF7a_0 NX7a_0 HC7a_0 SK7a_0 FC7a_0 FX7a_0 XC7a_0 HCO7a_0 WCO7a_0
           RB7a_0 HCR7a_0 LEN7a_0 PERM_nd7a_0 PERM_lt7a_0 PERM_cov7a_0 HCS7a_0 MRG7a_0 HCM7a_0 He7a_0 Hchk7a_0 HT7a_0 FBC7a_0 FBT7a_0 NXC7a_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY7 tY7. rewrite HD7a_0.
  revert rY7 tY7. apply (hint_low_triple 1%nat st nx0 BX D7a D7La (F_g8L nx0) WD7La_0 DD7La_0 NXD7La_0 HD7La_0 FLOW7a_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g8L_hold 1%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) ok A Kc rho a Q). intros rY7 tY7.
  apply (sec_g45 1%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXa FXPa (PXnba_0 G2) D7La U8a ET8a CT8a CO8a T8a s8a R8a
           WU8a_0 DU8a_0 NXU8a_0 HU8a_0 Cert8a_0 WC8a_0 DF8a_0 NX8a_0 HC8a_0 SK8a_0 FC8a_0 FX8a_0 XC8a_0 HCO8a_0 WCO8a_0
           He8a_0 Hchk8a_0 HT8a_0 FBC8a_0 FBT8a_0 NXC8a_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY8 tY8. rewrite HD8a_0.
  revert rY8 tY8. apply (hint_low_triple 1%nat st nx0 BX D8a D8La (F_g9L nx0) WD8La_0 DD8La_0 NXD8La_0 HD8La_0 FLOW8a_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g9L_hold 1%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) ok A Kc rho a Q). intros rY8 tY8.
  apply (sec_g46 1%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXa FXPa (PXnba_0 G2) D8La U9a E9fa E9pa CO9pa E9qa
           WU9a_0 DU9a_0 NXU9a_0 HU9a_0 Cert9a_0 SK9a_0 FC9a_0 FX9a_0 FP9a_0 XC9a_0 HCO9a_0 WCO9a_0 Cert9qa_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  - intros rY9 tY9.
    apply (sec_g47 1%nat st nx0 BX E9fa S9afa S9bfa D9fa iMfa perm9fa HS9afa_0 HS9bfa_0 HD9fa_0 NDpfa_0 BNDpfa_0 COVpfa_0 ok A Kc rho a Q).
    intros rZ tZ.
    exact (sec_g48_P 1%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXoka_0 G2) 131072 DZero (SAlu ALU_ADD (SVar V_NRES) (SLit 16384)) FXPa ltac:(first [left; reflexivity | right; reflexivity]) (HPATHa_0 G2)
             false FFfa swcfa c1fa c2fa c4fa c5fa mcfa xcfa tybfa SELFfa_0 NDFfa_0 BNDFfa_0 COVFfa_0 XFnfa_0 BFbfa_0 FPFfa_0 FXFfa_0 FPARfa_0
             Hc1fa_0 Hmcfa_0 Htybfa_0 Hxcfa_0 WCUfa_0 SELUfa_0 NDUfa_0 BNDUfa_0 COVUfa_0 W9fa_0 D9fa_0 XB9fa_0 sFfa ENT9fa_0 SID9fa_0 G110fa_0 D9fa CertFfa_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
  - intros rY9 tY9.
    apply (sec_g47 1%nat st nx0 BX E9qa S9aqa S9bqa D9qa iMqa perm9qa HS9aqa_0 HS9bqa_0 HD9qa_0 NDpqa_0 BNDpqa_0 COVpqa_0 ok A Kc rho a Q).
    intros rZ tZ.
    exact (sec_g48_P 1%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXoka_0 G2) 131072 DZero (SAlu ALU_ADD (SVar V_NRES) (SLit 16384)) FXPa ltac:(first [left; reflexivity | right; reflexivity]) (HPATHa_0 G2)
             true FFqa swcqa c1qa c2qa c4qa c5qa mcqa xcqa tybqa SELFqa_0 NDFqa_0 BNDFqa_0 COVFqa_0 XFnqa_0 BFbqa_0 FPFqa_0 FXFqa_0 FPARqa_0
             Hc1qa_0 Hmcqa_0 Htybqa_0 Hxcqa_0 WCUqa_0 SELUqa_0 NDUqa_0 BNDUqa_0 COVUqa_0 W9qa_0 D9qa_0 XB9qa_0 sFqa ENT9qa_0 SID9qa_0 G110qa_0 D9qa CertFqa_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
Qed.

Theorem sec_tail_1la : ltac2:(tb__ "0|8|
S37OF_;S15S2aS8S8S27Q40M0A1M1S0G1A1M2S16S45VW;Vst;A2S2bR7A1S3bS1fRaS3aR8A1A3S7S1bG1S9R8R1A2S9R9R1A2A3Fi;S7S1bS0S27Q8A1M3A1ScR9R1A2ScRaR1A2A3Fl;S2cVCST;VXGL;RcRcSaRaA1SaR9A1A6S20S23S2S18S17RdA1A2A1S19RdA1A2S1S6S6A2M4S32G4R1S42R9A1A3S40R2S3S6S6S28G0RcA2M5S44S28G0S9RdPcA2A2A1M6A4A2F_;Fbn;S6S1cS20S3fG5A1M7R1A2S24R1S21G7S22G6Z8A2A2A2A2S1dS1bS5G3A1SaReS29G0R2A2A2S4G3A1A3A1F_;Fz;S8G2S36S1fR13S39S1fS2dU1Vst;S2fS26S15S33R1A1LX;RcA2R12R11RfReA8S4bR2R1A5S3dS1fS38R10RdS49VCST;VXGL;VW;Vst;R12R11A6A5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 G2. exact (sec_tail_0la_P ok A Kc rho0 rho a tp0 G2 (PFc CST XGL W st A Kc) (or_intror (or_introl eq_refl))).
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

Theorem sec_tail_0lb_P : ltac2:(tb__ "0|9|
S37OF_;S15S2aS8S8S27Q40M0A1M1S0G1A1M2S16S0S1S3cS3eA2M3A1S32G3S3S3cS3eS48VW;Vst;A2S47VCST;VXGL;R8R7A4A4R1A3S45VW;Vst;A2S2bR9A1S3bS1fRcS3aRaA1A3S7S1bG1S9RaR1A2S9RbR1A2A3Fi;S7S1bS0S27Q8A1M4A1ScRbR1A2ScRcR1A2A3Fl;S2cVCST;VXGL;ReReSaRcA1SaRbA1A6S20S23S2S18S17RfA1A2A1S19RfA1A2S1S6S6A2M5S32G5R1S42RbA1A3S40R2S3S6S6S28G0ReA2M6S44S28G0S9RfPcA2A2A1M7A4A2F_;Fbn;S6S1cS20S3fG6A1M8R1A2S24R1S21G8S22G7Z8A2A2A2A2S1dS1bS5G4A1SaR10S29G0R2A2A2S4G4A1A3A1F_;Fz;S8G2S36S1fR15S39S1fS2dU1Vst;S2fS26S15R1LX;ReA2R14R13R11R10A8S4cR2R1A5S3dS1fS38R12RfRdA5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 G2 Posts HPin HUS HKc Hokl HLw HLl HKEPT HL9 HDB RUNDEF.
  set (BX := AXK (fun X : AA => X) G2). set (Q := LQPA segsA NF rho0 tp0 Posts).
  assert (HW : stopJ_w W st) by (hw_discharge).
  assert (BXg : forall X, aa_geom (BX X) = aa_geom X) by (intros X; reflexivity).
  apply (sec_g43_low 1%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXb FXPb (PXnbb_0 G2) C5bc C5Ab Y6Ab E6b CT6b CO6b T6b s6Ab s6b R6b
           FLOWb_0 HC5Ab_0 FBAb_0 Cert6Ab_0 E6Ab_0 I6Ab_0
           WC6b_0 DF6b_0 NX6b_0 HC6b_0 SK6b_0 FC6b_0 FX6b_0 XC6b_0 HCO6b_0 WCO6b_0 He6b_0 Hchk6b_0 HT6b_0 FBC6b_0 FBT6b_0 NXC6b_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY6 tY6. rewrite HD6b_0.
  revert rY6 tY6. apply (hint_low_triple 1%nat st nx0 BX D6b D6Lb (F_g7L nx0) WD6Lb_0 DD6Lb_0 NXD6Lb_0 HD6Lb_0 FLOW6b_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g7L_hold 1%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) ok A Kc rho a Q). intros rY6 tY6.
  apply (sec_g44 1%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXb FXPb (PXnbb_0 G2) D6Lb U7b ET7b CT7b CO7b CR7b CS7b CM7b T7b s7b R7b n7b
           WU7b_0 DU7b_0 NXU7b_0 HU7b_0 Cert7b_0 WC7b_0 DF7b_0 NX7b_0 HC7b_0 SK7b_0 FC7b_0 FX7b_0 XC7b_0 HCO7b_0 WCO7b_0
           RB7b_0 HCR7b_0 LEN7b_0 PERM_nd7b_0 PERM_lt7b_0 PERM_cov7b_0 HCS7b_0 MRG7b_0 HCM7b_0 He7b_0 Hchk7b_0 HT7b_0 FBC7b_0 FBT7b_0 NXC7b_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY7 tY7. rewrite HD7b_0.
  revert rY7 tY7. apply (hint_low_triple 1%nat st nx0 BX D7b D7Lb (F_g8L nx0) WD7Lb_0 DD7Lb_0 NXD7Lb_0 HD7Lb_0 FLOW7b_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g8L_hold 1%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) ok A Kc rho a Q). intros rY7 tY7.
  apply (sec_g45 1%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXb FXPb (PXnbb_0 G2) D7Lb U8b ET8b CT8b CO8b T8b s8b R8b
           WU8b_0 DU8b_0 NXU8b_0 HU8b_0 Cert8b_0 WC8b_0 DF8b_0 NX8b_0 HC8b_0 SK8b_0 FC8b_0 FX8b_0 XC8b_0 HCO8b_0 WCO8b_0
           He8b_0 Hchk8b_0 HT8b_0 FBC8b_0 FBT8b_0 NXC8b_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  intros rY8 tY8. rewrite HD8b_0.
  revert rY8 tY8. apply (hint_low_triple 1%nat st nx0 BX D8b D8Lb (F_g9L nx0) WD8Lb_0 DD8Lb_0 NXD8Lb_0 HD8Lb_0 FLOW8b_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g9L_hold 1%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) ok A Kc rho a Q). intros rY8 tY8.
  apply (sec_g46 1%nat st tmax nx0 Hnx_0 NXG_0 BX BXg PXb FXPb (PXnbb_0 G2) D8Lb U9b E9fb E9pb CO9pb E9qb
           WU9b_0 DU9b_0 NXU9b_0 HU9b_0 Cert9b_0 SK9b_0 FC9b_0 FX9b_0 FP9b_0 XC9b_0 HCO9b_0 WCO9b_0 Cert9qb_0
           ok A Kc rho a Q HW HUS HKc Hokl RUNDEF).
  - intros rY9 tY9.
    apply (sec_g47 1%nat st nx0 BX E9fb S9afb S9bfb D9fb iMfb perm9fb HS9afb_0 HS9bfb_0 HD9fb_0 NDpfb_0 BNDpfb_0 COVpfb_0 ok A Kc rho a Q).
    intros rZ tZ.
    exact (sec_g48_P 1%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXokb_0 G2) 8 DUnknown (SVar V_NRES) FXPb ltac:(first [left; reflexivity | right; reflexivity]) (HPATHb_0 G2)
             false FFfb swcfb c1fb c2fb c4fb c5fb mcfb xcfb tybfb SELFfb_0 NDFfb_0 BNDFfb_0 COVFfb_0 XFnfb_0 BFbfb_0 FPFfb_0 FXFfb_0 FPARfb_0
             Hc1fb_0 Hmcfb_0 Htybfb_0 Hxcfb_0 WCUfb_0 SELUfb_0 NDUfb_0 BNDUfb_0 COVUfb_0 W9fb_0 D9fb_0 XB9fb_0 sFfb ENT9fb_0 SID9fb_0 G110fb_0 D9fb CertFfb_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
  - intros rY9 tY9.
    apply (sec_g47 1%nat st nx0 BX E9qb S9aqb S9bqb D9qb iMqb perm9qb HS9aqb_0 HS9bqb_0 HD9qb_0 NDpqb_0 BNDpqb_0 COVpqb_0 ok A Kc rho a Q).
    intros rZ tZ.
    exact (sec_g48_P 1%nat st tmax nx0 Hnx_0 NXG_0 CST XGL HCST HXGL HCSTM HCSTS BX (BXokb_0 G2) 8 DUnknown (SVar V_NRES) FXPb ltac:(first [left; reflexivity | right; reflexivity]) (HPATHb_0 G2)
             true FFqb swcqb c1qb c2qb c4qb c5qb mcqb xcqb tybqb SELFqb_0 NDFqb_0 BNDFqb_0 COVFqb_0 XFnqb_0 BFbqb_0 FPFqb_0 FXFqb_0 FPARqb_0
             Hc1qb_0 Hmcqb_0 Htybqb_0 Hxcqb_0 WCUqb_0 SELUqb_0 NDUqb_0 BNDUqb_0 COVUqb_0 W9qb_0 D9qb_0 XB9qb_0 sFqb ENT9qb_0 SID9qb_0 G110qb_0 D9qb CertFqb_0
             ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT HL9 HDB rZ tZ).
Qed.

Theorem sec_tail_1lb : ltac2:(tb__ "0|8|
S37OF_;S15S2aS8S8S27Q40M0A1M1S0G1A1M2S16S45VW;Vst;A2S2bR7A1S3bS1fRaS3aR8A1A3S7S1bG1S9R8R1A2S9R9R1A2A3Fi;S7S1bS0S27Q8A1M3A1ScR9R1A2ScRaR1A2A3Fl;S2cVCST;VXGL;RcRcSaRaA1SaR9A1A6S20S23S2S18S17RdA1A2A1S19RdA1A2S1S6S6A2M4S32G4R1S42R9A1A3S40R2S3S6S6S28G0RcA2M5S44S28G0S9RdPcA2A2A1M6A4A2F_;Fbn;S6S1cS20S3fG5A1M7R1A2S24R1S21G7S22G6Z8A2A2A2A2S1dS1bS5G3A1SaReS29G0R2A2A2S4G3A1A3A1F_;Fz;S8G2S36S1fR13S39S1fS2dU1Vst;S2fS26S15R1LX;RcA2R12R11RfReA8S4cR2R1A5S3dS1fS38R10RdS49VCST;VXGL;VW;Vst;R12R11A6A5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 G2. exact (sec_tail_0lb_P ok A Kc rho0 rho a tp0 G2 (PFc CST XGL W st A Kc) (or_intror (or_introl eq_refl))).
Qed.
End INST.
End SpineCallocSec6JLW1.

(* [comment removed for export] *)
Module CallocHit1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineCallocI2"; "rho_c"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@Corelib.Init.Logic"; "False"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "JLc_ok"; "Lc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1"; "E_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "E3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "J_alloc_preT"; "KcA"; "Kc_ok"; "Pre_callocI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI"; "Jc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Stdlib.Lists.List"; "In"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "mul"; "pow"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ap.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS5iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS6iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.SpineCallocS7iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS8iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocS9iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3c OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineCallocS5t OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cu.CallocHitTail1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ap.CertCallocS1c OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS1iW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS12iW1.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section HIT0.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S0SaVCST;R1A2SaS23R2A2S14F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S0SaVCST;R1A2S16S24R2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S1eVAInv;VW;Vst;VA;VKc;S6PcA1A6").
Let law_die : forall A rho tp md, AInv A rho tp md -> cell_ok (view segs (rm rho)) (mkACell 0x182f1c 4 0) := AInvA_die.
Let W0 : list ulink := Wcan 1.
Let st0 : ustop := UStopLeOrPc.

Theorem calloc_hit_1_P : ltac2:(tb__ "0|5|
S3OF_;S22S1fS5SeSdQ40M0A1A1SeS10S11S12A2M1A1S13Vsegs;S17SbR3A1R2R1A5S2S28G1SfS11S12S1aVW0;Vst0;A2S19VCST;VXGL;R6R5A4A4R2A3S20R6A1S9Vsegs;R9S8R7A1A3S18Vsegs;RaS8R8A1A3S29S2aScG0S4R8PcM2A2A2ScG0S4R8PdA2A2A2S2bZ2Z40A2A2S15S0S26RbScG0S4SbR9A1G2A2A2A2Z0A3S5S1Vsegs;ReS7Vsegs;S27VW0;Vst0;RdRcSbRbA1A5M3S1cVW0;Vst0;Z3M4A3R1RaA5R8A4FrhoE;F_;S5S1Vsegs;ReS7Vsegs;G3S1bVW0;Vst0;G4Z8A4R1RaA5R8A4FrhoE;S1Vsegs;ReS7Vsegs;S25VW0;Vst0;RdRcA4S21S1dVW0;Vst0;A3RbRaA5R8A4F_;F_;F_;F_;F_;F_;F_;TQ;FPosts;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Posts Q HPin HKc Hokl Hokpl Hmul HREF HSEC.
  assert (Hokf : forall A', ok_frameA segs ok (J W0 st0 A' Kc)).
  { intros A' r t tr ms md msv' HJ. apply (Hokl r t tr ms md msv'). destruct HJ as (_ & HK & _). exact HK. }
  pose proof HUS_c as HUS.
  assert (HW : stopJ_w W0 st0) by (hw_discharge).
  apply (spine_s1c_pc law_die 1%nat st0 3 WC1_0 DC1_0 WE1_c DE1_c HSW_c HUS_c Wa_c Da_c Wb_c Fbh_c Fbl_c ENTh_c ENTl_c s1_cert_1 Est_c WPC_c DPC_c HWne_c ok A Kc rho tp Q HKc (Hokf A) Hmul); [|exact HSEC].
  intros rhoE1.
  apply (spine_s2c 1%nat st0 3 Cert2_0 OVa_0 OVb_0 TABa_0 TABb_0 Wa'_0 Wb'_0 Da'_0 Db'_0 NXa_0 NXb_0 Fa_0 Fb_0 Ga_0 Gb_0 SKa_0 SKb_0 XXa_0 XXb_0 XFa_0 XFb_0
           W1a_0 W1ba_0 W1ca_0 W2a_0 W1ra_0 W2ra_0 W1b_0 W1bb_0 W1cb_0 W2b_0 W1rb_0 W2rb_0 sa_0 sra_0 sb_0 srb_0 ENTa_0 ENTra_0 ENTb_0 ENTrb_0
           SIDa_0 SIDra_0 SIDb_0 SIDrb_0 FB_0 FBr_0 ok A Kc (rho_c rho) tp Q HW HUS HKc (Hokf A)).
  2: { intros Hz0 rhoE2. apply (spine_s3r 1%nat st0 3 Cert3r_0 ok A Kc (rho_c rho) tp Q HUS HKc (Hokf A)). exact (HREF Hz0). }
  intros rhoE2.
  apply (spine_s3p_cert 1%nat st0 3 Cert3p_0 ok A Kc (rho_c rho) tp Q HUS HKc (Hokf A)).
  exact (calloc_hit_tail_1_P CST XGL HCST HXGL HCSTM HCSTD ok A Kc (rho_c rho) tp Posts HPin HKc Hokl Hokpl).
Qed.
End HIT0.
End CallocHit1.

