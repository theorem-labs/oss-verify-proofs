(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_scene (asan). The class-8 stack-free contract
   `astack_free_realizes tfibsegs B PC_STACK_FREE_8 CID8` (lib/Reusable/StackFreeDef.v), closed: this file
   applies a Theorem Labs lane's proved top lib/A/Rt/StackFree8Tbl.v `sce_stack_free_8` (the walk is
   lib/Reusable/StackFree8.v), and proves nothing new about any function.

   Two theorems:
   - `stack_free_8_closed`: the premises are exactly the three Section hypotheses of `sce_stack_free_8`, in its
     order: AR_laws, and the two callee summaries of lib/Reusable/AsStackLeaf.v (MemToShadow at
     PC_MEM_TO_SHADOW = 0x3f5d8, PoisonShadow at PC_POISON_SHADOW = 0x55bb8; both from
     lib/A/Rt/StackMalloc8Tbl.v).
   - `stack_free_8_discharged`: the two summary premises are discharged by a Theorem Labs lane's proved summaries
     (lib/A/RT_mem_to_shadow.v `scene_mem_to_shadow` at M2S_ENTRY = PC_MEM_TO_SHADOW = 0x3f5d8, and
     lib/A/RT_poison_shadow.v `scene_poison_shadow` at PS_ENTRY = PC_POISON_SHADOW = 0x55bb8), which need
     A/AF0m.v's TfibSyms B. Its premises are AR_laws and TfibSyms: facts about B's certificate only.
     No Axiom, no Admitted, no admit. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0t YCe5.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import StackFreeDef AsStackLeaf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AF0m RT_mem_to_shadow RT_poison_shadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import StackMalloc8Tbl StackFree8Tbl.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
Import ListNotations.
Open Scope Z_scope.

Theorem stack_free_8_closed {fx : YK11.FPState} {rc : YM05.RunCeil} (B : asyms) :
AR_laws tfibsegs B ->
mem_to_shadow_realizes tfibsegs B PC_MEM_TO_SHADOW ->
poison_shadow_realizes tfibsegs B PC_POISON_SHADOW ->
astack_free_realizes tfibsegs B PC_STACK_FREE_8 CID8.
Proof.
intros LAWS MTS_SUM PS_SUM.
exact (StackFree8Tbl.sce_stack_free_8 B LAWS MTS_SUM PS_SUM).
Qed.

Theorem stack_free_8_discharged {fx : YK11.FPState} {rc : YM05.RunCeil} (B : asyms) :
AR_laws tfibsegs B ->
AF0m.PcapSyms B ->
astack_free_realizes tfibsegs B PC_STACK_FREE_8 CID8.
Proof.
intros LAWS TB.
apply stack_free_8_closed; try assumption.
- change PC_MEM_TO_SHADOW with RT_mem_to_shadow.M2S_ENTRY.
  apply RT_mem_to_shadow.scene_mem_to_shadow; assumption.
- change PC_POISON_SHADOW with RT_poison_shadow.PS_ENTRY.
  apply RT_poison_shadow.scene_poison_shadow; assumption.
Qed.
