(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes
  PureModel VmLedger AllocIface.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocShape RefStep RefStmts.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require Import RefStepR.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Enframe.
Context {fx : FPState} {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL}.
#[local] Existing Instance reloc_layout.

Theorem enframe_refines : enframe_stmt.
Proof.
  unfold enframe_stmt.
  intros md regs mm rom s g idx n ctr sp ret P L Hp Hvm Hag H2 Hal Hlo0 Hlo Hhi Hhi64 Hwt Hstk H1 Hret H4 H10 H11 H12 H13 HS HK.
  pose proof (minv_init s sp 0 Hlo0 Hlo ltac:(lia) Hhi Hhi64 Hwt) as HI.
  pose proof (mwin_init s mm sp 0 Hstk) as HW.
  rewrite <- (with_vmmaps_same md), <- Hvm.
  unfold m_enframe in HS |- *. munf.
  (* [comment removed for export] *)
  mrun_until Hp HS Hag HI HW (bv_unsigned PC_ENFRAME + 0x8).
  mach_join Hp HS Hag HI HW (bv_unsigned PC_ENFRAME + 0x40) [14; 15]%Z [14]%Z.
  (* [comment removed for export] *)
  mrun_until Hp HS Hag HI HW (bv_unsigned PC_ENFRAME + 0x5c).
  mach_join Hp HS Hag HI HW (bv_unsigned PC_ENFRAME + 0x68) [13]%Z [13]%Z.
  (* [comment removed for export] *)
  mrun_until Hp HS Hag HI HW (bv_unsigned PC_ENFRAME + 0x7c).
  mach_join Hp HS Hag HI HW (bv_unsigned PC_ENFRAME + 0xb8) [13; 5; 17]%Z [17]%Z.
  (* [comment removed for export] *)
  mrun_until Hp HS Hag HI HW (bv_unsigned PC_ENFRAME + 0xbc).
  mach_join Hp HS Hag HI HW (bv_unsigned PC_ENFRAME + 0xdc) [16; 13]%Z [13; 16]%Z.
  (* [comment removed for export] *)
  mrun_until Hp HS Hag HI HW (bv_unsigned PC_ENFRAME + 0x100).
  mach_join Hp HS Hag HI HW (bv_unsigned PC_ENFRAME + 0x134) [10; 11; 12]%Z [10]%Z.
  mrun Hp HS Hag HI HW.
  mach_ret Hp HS Hag HK HI Hret.
Qed.
End Enframe.
