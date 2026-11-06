(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes
  PureModel VmLedger AllocIface AsanCeil.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocShape RefLrSc RefStep RefStmts RefSys.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng Require Import RRef_getmeta.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng Require Import RefStepR.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section NtFree.
Context {fx : FPState} {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL}.
#[local] Existing Instance reloc_layout.

(* [comment removed for export] *)
Ltac nt_calls IH Hp HS Hag HI HW t :=
  let gm := rl_name_of (bv_unsigned PC_GET_META)%Z in
  let nt := rl_name_of (bv_unsigned PC_NTFREE)%Z in
  tryif constr_eq t gm then mach_call Hp HS Hag HI HW (get_meta_refines (fx:=_))
  else tryif constr_eq t nt then mach_call Hp HS Hag HI HW IH
  else mach_jal Hp HS.

Theorem ntfree_refines : ntfree_stmt.
Proof.
  unfold ntfree_stmt. intros md regs mm rom s fuel. revert md regs mm rom s.
  induction fuel as [|fuel IH];
    intros md regs mm rom s g i sp ret P L Hp Hvm Hag H2 Hal Hlo0 Hlo Hhi Hhi64 Hwt Hstk H1 Hret H4 H10 H11 HS HK.
  { (* [comment removed for export] *) exfalso. exact HS. }
  rewrite Nat2Z.inj_succ in Hlo, Hstk, HK.
  pose proof (minv_init s sp (96 * Z.succ (Z.of_nat fuel)) Hlo0 Hlo ltac:(lia) Hhi Hhi64 Hwt) as HI.
  pose proof (mwin_init s mm sp (96 * Z.succ (Z.of_nat fuel)) Hstk) as HW.
  rewrite <- (with_vmmaps_same md), <- Hvm.
  note_win HI.
  unfold m_nontrivial_free in HS |- *. fold m_nontrivial_free in HS |- *.
  munf. mnorm HS.
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret ltac:(nt_calls IH) (bv_unsigned PC_NTFREE + 0x28). mark_frame 48.
  mrunx_until Hp HS Hag HI HW HK Hret ltac:(nt_calls IH) (bv_unsigned PC_NTFREE + 0x4c).
  mach_join_bool Hp HS Hag HI HW (bv_unsigned PC_NTFREE + 0x114) (bv_unsigned PC_NTFREE + 0x15c) [5;14;15;16;17;18]%Z
    (fun (x : bool) (R' : bvmap 5 word) => if x then getr R' 18 = A_CTX else True).
  2: { (* [comment removed for export] *)
    mrunx_until Hp HS Hag HI HW HK Hret ltac:(nt_calls IH) (bv_unsigned PC_NTFREE + 0x160).
    mach_join Hp HS Hag HI HW (bv_unsigned PC_NTFREE + 0x380) [12;13;15]%Z (@nil Z).
    mrunx Hp HS Hag HI HW HK Hret ltac:(nt_calls IH). }
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret ltac:(nt_calls IH) (bv_unsigned PC_NTFREE + 0x118).
  mach_join Hp HS Hag HI HW (bv_unsigned PC_NTFREE + 0x228) [5;11;12;13;14;15;16;17]%Z (@nil Z).
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret ltac:(nt_calls IH) (bv_unsigned PC_NTFREE + 0x238).
  mach_join Hp HS Hag HI HW (bv_unsigned PC_NTFREE + 0x25c) [12;13;14]%Z [12]%Z.
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret ltac:(nt_calls IH) (bv_unsigned PC_NTFREE + 0x260).
  mstepx Hp HS Hag HI HW HK Hret ltac:(nt_calls IH).
  2: { (* [comment removed for export] *)
    mrunx_until Hp HS Hag HI HW HK Hret ltac:(nt_calls IH) (bv_unsigned PC_NTFREE + 0x29c).
    mach_join Hp HS Hag HI HW (bv_unsigned PC_NTFREE + 0x2bc) [12;13]%Z [12]%Z.
    mrunx_until Hp HS Hag HI HW HK Hret ltac:(nt_calls IH) (bv_unsigned PC_NTFREE + 0x2c8).
    mach_join Hp HS Hag HI HW (bv_unsigned PC_NTFREE + 0x2d4) [11]%Z (@nil Z).
    mrunx_until Hp HS Hag HI HW HK Hret ltac:(nt_calls IH) (bv_unsigned PC_NTFREE + 0x33c).
    mach_join Hp HS Hag HI HW (bv_unsigned PC_NTFREE + 0x3a8) [13;18]%Z (@nil Z).
    mrunx Hp HS Hag HI HW HK Hret ltac:(nt_calls IH). }
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret ltac:(nt_calls IH) (bv_unsigned PC_NTFREE + 0x33c).
  mach_join Hp HS Hag HI HW (bv_unsigned PC_NTFREE + 0x3a8) [13;18]%Z (@nil Z).
  mrunx Hp HS Hag HI HW HK Hret ltac:(nt_calls IH).
Qed.
End NtFree.
