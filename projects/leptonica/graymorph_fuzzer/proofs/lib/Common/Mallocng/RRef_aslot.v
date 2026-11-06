(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import decidable.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes
  PureModel VmLedger AllocIface AsanCeil AgentLib.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocShape RefLrSc RefStep RefStmts RefSys RefPieces RefStep3.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require Import RRef_syswrap RRef_enframe RRef_ameta RRef_loops RRef_aslot1 RRef_aslot2 RRef_aslot3 RRef_aslot4.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require Import RefStepR.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac sys_hyps :=
  pose proof (mmap_refines (fx:=_)) as MM; pose proof (mmap_fixed_refines (fx:=_)) as MF;
  pose proof (mprotect_refines (fx:=_)) as MP; pose proof (munmap_refines (fx:=_)) as MU.
Ltac as_calls Hp HS Hag HI HW t :=
  sys_calls Hp HS Hag HI HW t ltac:(fun t =>
    let am := rl_name_of (bv_unsigned PC_ALLOC_META)%Z in
    let en := rl_name_of (bv_unsigned PC_ENFRAME)%Z in
    let asl := rl_name_of (bv_unsigned PC_ALLOC_SLOT)%Z in
    tryif constr_eq t am then mach_call Hp HS Hag HI HW (alloc_meta_refines (fx:=_))
    else tryif constr_eq t en then mach_call Hp HS Hag HI HW (enframe_refines (fx:=_))
    else tryif constr_eq t asl then match goal with REC : aslot_at _ |- _ => mach_call Hp HS Hag HI HW REC end
    else mach_jal Hp HS).

Section AllocSlot.
Context {fx : FPState} {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL}.
#[local] Existing Instance reloc_layout.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem alloc_slot_refines_at : forall fuel, aslot_at fuel.
Proof.
  induction fuel as [|fuel IH].
  - unfold aslot_at. intros md regs mm rom s sc req sp ret P L Hp Hvm Hag H2 Hal Hlo0 Hlo Hhi Hhi64 Hwt Hstk H1 Hret H4 H10 H11 HS HK.
    exfalso. clear -HS. cbn [m_alloc_slot mcrash tsafe] in HS. exact HS.
  - unfold aslot_at. intros md regs mm rom s sc req sp ret P L Hp Hvm Hag H2 Hal Hlo0 Hlo Hhi Hhi64 Hwt Hstk H1 Hret H4 H10 H11 HS HK.
    rewrite alloc_slot_D_S in Hlo, Hstk, HK.
    pose proof (alloc_slot_D_ge fuel) as HDge.
    pose proof (minv_init s sp (alloc_slot_D fuel + 144) Hlo0 Hlo ltac:(lia) Hhi Hhi64 Hwt) as HI.
    pose proof (mwin_init s mm sp (alloc_slot_D fuel + 144) Hstk) as HW.
    rewrite <- (with_vmmaps_same md), <- Hvm. note_win HI. sys_hyps.
    rewrite (m_alloc_slot_pieces fuel) in HS |- *.
    munf. mnorm HS.
    (* [comment removed for export] *)
    mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x54). mark_frame 96.
    mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x58).
    use_piece (as_res_piece fuel) Hp Hag HI HW HS.
    intros res HX HS. mnorm HS.
    (* [comment removed for export] *)
    mrunx Hp HS Hag HI HW HK Hret as_calls.
Qed.

Theorem alloc_slot_refines : alloc_slot_stmt.
Proof. apply alloc_slot_stmt_of_at. exact alloc_slot_refines_at. Qed.

End AllocSlot.
