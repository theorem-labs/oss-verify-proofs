(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import decidable.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes
  PureModel VmLedger AllocIface AsanCeil AgentLib.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocShape RefLrSc RefStep RefStmts RefSys RefPieces RefStep3.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require Import RRef_syswrap RRef_enframe RRef_ameta RRef_aslot.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require Import RefStepR.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Malloc.
Context {fx : FPState} {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL}.
#[local] Existing Instance reloc_layout.

(* [comment removed for export] *)
Lemma alloc_slot_refines5 : forall md regs mm rom (s : mstate) (sc req sp ret : word)
         (P : word -> mstate -> Prop) (L : word -> mstate -> TSet),
  md_pure md -> ms_vm s = m_vmmaps md -> magree s mm ->
  getr regs 2 = sp -> bv_unsigned sp mod 16 = 0 ->
  0 <= ms_lo s -> ms_lo s <= bv_unsigned sp - 864 -> bv_unsigned sp <= ms_hi s -> ms_hi s <= 2^64 ->
  wtop s ->
  (forall a, bv_unsigned sp - 864 <= bv_unsigned a < bv_unsigned sp -> mm a <> None) ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = A_TP ->
  getr regs 10 = sc -> getr regs 11 = req ->
  tsafe (m_alloc_slot ALLOC_FUEL (at_ sp (-144)) sc req s) P ->
  (forall r s' mm' regs',
     P r s' -> magree s' mm' -> ms_lo s' = ms_lo s -> ms_hi s' = ms_hi s ->
     alloc_top (ms_vm s') = alloc_top (ms_vm s) ->
     getr regs' 10 = r -> getr regs' 2 = sp ->
     (forall x, callee_saved x -> getr regs' x = getr regs x) ->
     (forall a, ms_lo s <= bv_unsigned a < ms_hi s ->
                ~ (bv_unsigned sp - 864 <= bv_unsigned a < bv_unsigned sp) -> mm' a = mm a) ->
     (forall a, bv_unsigned sp - 864 <= bv_unsigned a < bv_unsigned sp -> mm' a <> None) ->
     realizes ml_segs (mkCfg (mkst regs' ret mm' rom) (with_vmmaps (ms_vm s') md)) (L r s')) ->
  realizes ml_segs (mkCfg (mkst regs PC_ALLOC_SLOT mm rom) md)
           (tshape (m_alloc_slot ALLOC_FUEL (at_ sp (-144)) sc req s) L).
Proof. intros. eapply (alloc_slot_refines md regs mm rom s ALLOC_FUEL); eassumption. Qed.

Ltac sys_hyps :=
  pose proof (mmap_refines (fx:=_)) as MM; pose proof (mmap_fixed_refines (fx:=_)) as MF;
  pose proof (mprotect_refines (fx:=_)) as MP; pose proof (munmap_refines (fx:=_)) as MU.
Ltac malloc_calls Hp HS Hag HI HW t :=
  sys_calls Hp HS Hag HI HW t ltac:(fun t =>
    let am := rl_name_of (bv_unsigned PC_ALLOC_META)%Z in
    let asl := rl_name_of (bv_unsigned PC_ALLOC_SLOT)%Z in
    tryif constr_eq t am then mach_call Hp HS Hag HI HW (alloc_meta_refines (fx:=_))
    else tryif constr_eq t asl then mach_call Hp HS Hag HI HW alloc_slot_refines5
    else mach_jal Hp HS).

Theorem malloc_refines : malloc_stmt.
Proof.
  unfold malloc_stmt.
  intros md regs mm rom s n sp ret P L Hp Hvm Hag H2 Hal Hlo0 Hlo Hhi Hhi64 Hwt Hstk H1 Hret H4 H10 HS HK.
  unfold ALLOC_STACK in *.
  pose proof (minv_init s sp 1024 Hlo0 Hlo ltac:(lia) Hhi Hhi64 Hwt) as HI.
  pose proof (mwin_init s mm sp 1024 Hstk) as HW.
  rewrite <- (with_vmmaps_same md), <- Hvm. note_win HI. sys_hyps.
  unfold m_malloc in HS |- *. munf.
  mrunx_until Hp HS Hag HI HW HK Hret malloc_calls (bv_unsigned PC_MALLOC_IMPL + 0x1c). mark_frame 48.
  mrunx_until Hp HS Hag HI HW HK Hret malloc_calls (bv_unsigned PC_MALLOC_IMPL + 0x70).
  mstepx Hp HS Hag HI HW HK Hret malloc_calls.
  2: { (* [comment removed for export] *)
    mrunx_until Hp HS Hag HI HW HK Hret malloc_calls (bv_unsigned PC_MALLOC_IMPL + 0xc0).
    mach_join Hp HS Hag HI HW (bv_unsigned PC_MALLOC_IMPL + 0x184) [10]%Z [10]%Z.
    mrunx Hp HS Hag HI HW HK Hret malloc_calls.
    mach_tailcall Hp HS Hag HI HW HK (enframe_refines (fx:=_)).
    all: mach_tailcall Hp HS Hag HI HW HK (enframe_refines (fx:=_)). }
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret malloc_calls (bv_unsigned PC_MALLOC_IMPL + 0xf0).
  mach_join Hp HS Hag HI HW (bv_unsigned PC_MALLOC_IMPL + 0x1f4) [10;11;12;13;20]%Z [20]%Z.
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret malloc_calls (bv_unsigned PC_MALLOC_IMPL + 0x21c).
  mach_join_k Hp HS Hag HI HW HK Hret malloc_calls (word * option word)%type
    (fun x : word * option word => match snd x with Some _ => (pc+ PC_MALLOC_IMPL 0x2b8) | None => (pc+ PC_MALLOC_IMPL 0x2c4) end)
    [10;11;12;13;18;20]%Z
    (fun (x : word * option word) (R' : bvmap 5 word) =>
       getr R' 20 = fst x /\ match snd x with Some g => getr R' 18 = g | None => True end).
  intros [jsc [jg|]] [HX1 HX2] HS; cbv beta match delta [fst snd] in HX1, HX2; mnorm HS.
  - (* [comment removed for export] *)
    mach_join Hp HS Hag HI HW (bv_unsigned PC_MALLOC_IMPL + 0x2c8) [10]%Z [10]%Z.
    mrunx Hp HS Hag HI HW HK Hret malloc_calls.
    all: mach_tailcall Hp HS Hag HI HW HK (enframe_refines (fx:=_)).
  - (* [comment removed for export] *)
    mrunx Hp HS Hag HI HW HK Hret malloc_calls.
    all: mach_tailcall Hp HS Hag HI HW HK (enframe_refines (fx:=_)).
Qed.
End Malloc.
