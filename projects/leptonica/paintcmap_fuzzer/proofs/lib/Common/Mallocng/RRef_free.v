(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes
  PureModel VmLedger AllocIface AsanCeil.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocShape RefLrSc RefStep RefStmts RefSys.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require Import RRef_getmeta RRef_ntfree RRef_syswrap.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require Import RefStepR.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Free.
Context {fx : FPState} {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL}.
#[local] Existing Instance reloc_layout.

(* [comment removed for export] *)
Ltac free_calls Hp HS Hag HI HW t :=
  let gm := rl_name_of (bv_unsigned PC_GET_META)%Z in
  let nt := rl_name_of (bv_unsigned PC_NTFREE)%Z in
  let mu := rl_name_of (bv_unsigned PC_MUNMAP)%Z in
  tryif constr_eq t gm then mach_call Hp HS Hag HI HW (get_meta_refines (fx:=_))
  else tryif constr_eq t nt then mach_call Hp HS Hag HI HW (ntfree_refines (fx:=_))
  else tryif constr_eq t mu then mach_call Hp HS Hag HI HW (munmap_refines (fx:=_))
  else mach_jal Hp HS.

Theorem free_refines : free_stmt.
Proof.
  unfold free_stmt.
  intros md regs mm rom s p sp ret P L Hp Hvm Hag H2 Hal Hlo0 Hlo Hhi Hhi64 Hwt Hstk H1 Hret H4 H10 HS HK.
  unfold ALLOC_STACK in *.
  pose proof (minv_init s sp 1024 Hlo0 Hlo ltac:(lia) Hhi Hhi64 Hwt) as HI.
  pose proof (mwin_init s mm sp 1024 Hstk) as HW.
  rewrite <- (with_vmmaps_same md), <- Hvm.
  note_win HI.
  unfold m_free in HS |- *. munf.
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret free_calls (bv_unsigned PC_FREE + 0x24). mark_frame 40.
  mrunx_until Hp HS Hag HI HW HK Hret free_calls (bv_unsigned PC_FREE + 0x3c).
  mach_join Hp HS Hag HI HW (bv_unsigned PC_FREE + 0x74) [12; 14]%Z [12]%Z.
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret free_calls (bv_unsigned PC_FREE + 0x90).
  mach_join Hp HS Hag HI HW (bv_unsigned PC_FREE + 0xbc) [13; 14]%Z [14]%Z.
  (* [comment removed for export] *)
  mrunx Hp HS Hag HI HW HK Hret free_calls.
Qed.
End Free.
