(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import decidable.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes
  PureModel VmLedger AllocIface AsanCeil AgentLib.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocShape RefLrSc RefStep RefStmts RefSys RefPieces RefStep3.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng Require Import RefStepR.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section AllZeroP.
Context {fx : FPState} {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL}.
#[local] Existing Instance reloc_layout.

Theorem allzerop_refines : allzerop_stmt.
Proof.
  unfold allzerop_stmt.
  intros md regs mm rom s p sp ret P L Hp Hvm Hag H2 Hal Hlo0 Hlo Hhi Hhi64 Hwt Hstk H1 Hret H4 H10 HS HK.
  pose proof (minv_init s sp 0 Hlo0 Hlo ltac:(lia) Hhi Hhi64 Hwt) as HI.
  pose proof (mwin_init s mm sp 0 Hstk) as HW.
  rewrite <- (with_vmmaps_same md), <- Hvm.
  unfold m_allzerop, m_get_meta in HS |- *. munf.
  (* [comment removed for export] *)
  mnorm HS.
  mrun_until Hp HS Hag HI HW (bv_unsigned PC_ALLZEROP + 0x10c).
  all: mach_pload HS.
  (* [comment removed for export] *)
  all: mrun Hp HS Hag HI HW.
  all: mach_ret Hp HS Hag HK HI Hret.
Qed.
End AllZeroP.
