(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "AE_A"; "KcA"; "Kc_ok"; "Posts_malloc"; "Wcan"; "malloc_contractA"; "malloc_contractA_ex"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Corelib.Init.Datatypes"; "list"; "prod"; "@Corelib.Init.Logic"; "eq"; "False"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "E3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "vm_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2"; "IMG_S"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP RebuildM SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec SpineMallocSec2 TopGlueA MallocHit0 MallocHit0E.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ct.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require da.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.TopGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MallocHit0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MallocHit0E OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q1.MallocHit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dq.MallocHit2E OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cq.SpineMallocSecOK0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ct.SpineMallocSecOK0E OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cr.SpineMallocSecOK0W2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ct.SpineMallocSecOK0EW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.da.RefillPlug0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dv.RefillPlug2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section ASM.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S9ScVCST;R1A2ScS25R2A2S10F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S9ScVCST;R1A2ScS27R2A2S10F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S9ScVCST;R1A2S11S26R2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segsA.

Lemma law_res : ltac2:(tb__ "0|1|
S12SaSdS13Q40A1M0A1S1eVAInv;R4R3R2R1A4SfSdSeG0G0A2A1S20S1fR2A1A1S1dS0A1A3F_;Fmd;Ftp;Frho;FA;").
Proof. intros A rho tp md (_ & _ & _ & _ & HM & _). destruct HM as (_ & _ & _ & _ & _ & _ & _ & HL). exact (proj1 HL). Qed.

Definition HREF_stmt (nW : nat) (tmax : Z) : Prop := ltac2:(tb__ "0|2|
S23OF_;S12S3SaSdS13Q40M0A1A1S4R3A1S18S0R6S17R4A1A3S24S0R7S17R5A1A3SfS9S1bR7S14G0SbR5PcA2A2A2Z0A3SaS22S0RaS16S0S1cS6VnW;A1M1S1R9R8R7A5S1aG1S1Vtmax;A3R1R6A5S19S0S15R7R6S5S2VAInv;VCST;VXGL;G1S1R9R8A8A5A4FrhoE;F_;F_;F_;F_;Ftp;Frho;FKc;FA;Fok;").
Definition HREFE_stmt (nW : nat) (tmax : Z) : Prop := ltac2:(tb__ "0|2|
S12S3SaSdS13Q40M0A1A1S4R3A1SfS9S1bR5S14G0SbR3PcA2A2A2Z0A3SaS21S0S16S0S1cS6VnW;A1M1S1R7R6R5A5S1aG1S1Vtmax;A3R1R4A5S19S0S15R5R4S5S2VAInv;VCST;VXGL;G1S1R7R6A8A5A3FrhoE;F_;F_;Ftp;Frho;FKc;FA;").
Lemma HREF0 : HREF_stmt 0 2.
Proof. intros ok A Kc rho tp HKc Hokl Hokp Hcnt rhoE. exact (refill_all_0 CST XGL HCST HXGL HCSTM HCSTD ok A Kc rho tp HKc Hokl Hokp Hcnt rhoE). Qed.
Lemma HREF2 : HREF_stmt 2 4.
Proof. intros ok A Kc rho tp HKc Hokl Hokp Hcnt rhoE. exact (refill_all_2 CST XGL HCST HXGL HCSTM HCSTD ok A Kc rho tp HKc Hokl Hokp Hcnt rhoE). Qed.
Lemma HREFE0 : HREFE_stmt 0 2.
Proof. intros A Kc rho tp HKc Hcnt rhoE. exact (erefill_all_0 CST XGL HCST HXGL HCSTM HCSTD A Kc rho tp HKc Hcnt rhoE). Qed.
Lemma HREFE2 : HREFE_stmt 2 4.
Proof. intros A Kc rho tp HKc Hcnt rhoE. exact (erefill_all_2 CST XGL HCST HXGL HCSTM HCSTD A Kc rho tp HKc Hcnt rhoE). Qed.

Theorem malloc_contract_A : ltac2:(tb__ "0|0|
S7S0S2VAInv;VCST;VXGL;A5").
Proof.
  apply malloc_contractA_of_T. intros W st ok A Kc rho tp HW HKc Hokl Hokpl.
  destruct HW as [E|[E|[]]]; injection E as <- <-.
  - exact (malloc_hit_0 CST XGL HCST HXGL HCSTM HCSTD ok A Kc rho tp HKc Hokl Hokpl
             (fun Hz rhoE => HREF0 ok A Kc rho tp HKc Hokl Hokpl Hz rhoE)
             (malloc_sec_ok_0 CST XGL HCST HXGL HCSTM HCSTS HCSTD law_res ok A Kc rho tp HKc Hokl Hokpl)).
  - exact (malloc_hit_2 CST XGL HCST HXGL HCSTM HCSTD ok A Kc rho tp HKc Hokl Hokpl
             (fun Hz rhoE => HREF2 ok A Kc rho tp HKc Hokl Hokpl Hz rhoE)
             (malloc_sec_ok_2 CST XGL HCST HXGL HCSTM HCSTS HCSTD law_res ok A Kc rho tp HKc Hokl Hokpl)).
Qed.

Theorem malloc_contract_A_ex : ltac2:(tb__ "0|0|
S8S0S2VAInv;VCST;VXGL;A5").
Proof.
  apply malloc_contractA_ex_of_T. intros W st A Kc rho tp HW HKc.
  destruct HW as [E|[E|[]]]; injection E as <- <-.
  - exact (emalloc_hit_0 CST XGL HCST HXGL HCSTM HCSTD A Kc rho tp HKc
             (fun Hz rhoE => HREFE0 A Kc rho tp HKc Hz rhoE)
             (emalloc_sec_ok_0 CST XGL HCST HXGL HCSTM HCSTS HCSTD law_res A Kc rho tp HKc)).
  - exact (emalloc_hit_2 CST XGL HCST HXGL HCSTM HCSTD A Kc rho tp HKc
             (fun Hz rhoE => HREFE2 A Kc rho tp HKc Hz rhoE)
             (emalloc_sec_ok_2 CST XGL HCST HXGL HCSTM HCSTS HCSTD law_res A Kc rho tp HKc)).
Qed.
End ASM.
