(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "class_fresh"; "cls_keptA"; "cls_kept_freeA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.IfaceEx"; "classes_fresh_but_batch"; "classes_fresh"; "@Corelib.Init.Datatypes"; "list"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymSummary ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition classes_fresh (A : AA) : Prop := ltac2:(tb__ "0|0|
S5S6S4Z1R1A2S4R1Z1eA2A2S1VA;R2A2F_;Fc;").
Definition classes_fresh_but_batch (A : AA) : Prop := ltac2:(tb__ "0|0|
S5S6S4Z1R1A2S4R1Z1eA2A2S8S7S5R2Z18A3A1S1VA;R3A2F_;F_;Fc;").

Lemma fresh_kept_malloc_big : ltac2:(tb__ "0|1|
S0S0S5S4Zfc01R1A2S2R4R3R2A3SaR5A1M0G0F_;F_;F_;Fn;FA';FA;").
Proof. intros A A' n Hn HK HF c Hc. apply HK; [exact Hc | left; exact Hn | exact (HF c Hc)]. Qed.
Lemma fresh_but_batch_kept_malloc_big : ltac2:(tb__ "0|1|
S0S0S5S4Zfc01R1A2S2R4R3R2A3S9R5A1M0G0F_;F_;F_;Fn;FA';FA;").
Proof. intros A A' n Hn HK HF c Hc H24. apply HK; [exact Hc | left; exact Hn | exact (HF c Hc H24)]. Qed.
Lemma fresh_kept_free : ltac2:(tb__ "0|0|
S0S0S3R2R1A2SaR3A1S9R3A1F_;F_;FA';FA;").
Proof. intros A A' HK HF c Hc H24. exact (HK c Hc H24 (HF c Hc)). Qed.
Lemma fresh_but_batch_kept_free : ltac2:(tb__ "0|1|
S0S0S3R2R1A2S9R3A1M0G0F_;F_;FA';FA;").
Proof. intros A A' HK HF c Hc H24. exact (HK c Hc H24 (HF c Hc H24)). Qed.

Section WithSegs.
Variable segs : list Segment.
Variable E : aentry.
Variable AInvA : ltac2:(tb__ "0|0|
S0SdSbSeQ40A1A1ScOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).

Definition fresh_init_stmt (A0 : AA) : Prop := ltac2:(tb__ "0|0|
S5S6S4Z1R1A2S4R1Z1eA2A2S1VA0;R2A2F_;Fc;").

End WithSegs.
