(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import decidable.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes
  PureModel VmLedger AllocIface AsanCeil AgentLib.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocShape RefLrSc RefStep RefStmts RefSys RefPieces RefStep3
  RefCalloc.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import RRef_memset0 RRef_allzerop RRef_malloc.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import RefStepR.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac calloc_calls Hp HS Hag HI HW t :=
  let pm := rl_name_of (bv_unsigned PC_MALLOC)%Z in
  let pa := rl_name_of (bv_unsigned PC_ALLZEROP)%Z in
  let ps := rl_name_of (bv_unsigned PC_MEMSET)%Z in
  tryif constr_eq t pm then mach_call Hp HS Hag HI HW (malloc_refines (fx:=_))
  else tryif constr_eq t pa then mach_call Hp HS Hag HI HW (allzerop_refines (fx:=_))
  else tryif constr_eq t ps then mach_call Hp HS Hag HI HW (memset0_refines (fx:=_))
  else mach_jal Hp HS.

(* [comment removed for export] *)
Ltac on_pc off tac :=
  idtac;
  cur_pc ltac:(fun u =>
    let e := rl_name_of (bv_unsigned PC_CALLOC + off)%Z in
    tryif constr_eq u e then tac else idtac).

(* [comment removed for export] *)
Ltac loop_exit HK K Hag HI HS :=
  idtac;
  lazymatch goal with
  | |- realizes _ _ (tshape (K ?x ?sb) _) =>
      eapply (HK x sb); [ exact Hag | exact HI | win_same | keep_tac | val_tac | exact HS ]
  end.

Section Calloc.
Context {fx : FPState} {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL}.
#[local] Existing Instance reloc_layout.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zscan_run {B} : forall fuel (a1 a0 a2 : word) md (R : bvmap 5 word) mm rom (s0 s : mstate)
    (K : word * word -> M B) (P : B -> mstate -> Prop) (L : B -> mstate -> TSet),
  md_pure md -> magree s mm -> minv s0 s ->
  getr R 11 = a1 -> getr R 10 = a0 -> getr R 12 = a2 ->
  tsafe (MallocTree.mbind (m_zscan fuel a1 a0 a2) K s) P ->
  (forall (a0' a2' : word) (R' : bvmap 5 word),
     (forall r, wreg [10;12;13;14]%Z r = false -> getr R' r = getr R r) ->
     getr R' 10 = a0' -> getr R' 12 = a2' ->
     tsafe (K (v_sub a0' a2', a2') s) P ->
     realizes ml_segs (mkCfg (mkst R' (pc+ PC_CALLOC 0x98) mm rom) (with_vmmaps (ms_vm s) md))
              (tshape (K (v_sub a0' a2', a2') s) L)) ->
  (forall (a2' : word) (R' : bvmap 5 word),
     (forall r, wreg [10;12;13;14]%Z r = false -> getr R' r = getr R r) ->
     getr R' 12 = a2' ->
     tsafe (K (v_sub a1 a2', a2') s) P ->
     realizes ml_segs (mkCfg (mkst R' (pc+ PC_CALLOC 0xd8) mm rom) (with_vmmaps (ms_vm s) md))
              (tshape (K (v_sub a1 a2', a2') s) L)) ->
  realizes ml_segs (mkCfg (mkst R (pc+ PC_CALLOC 0xbc) mm rom) (with_vmmaps (ms_vm s) md))
           (tshape (MallocTree.mbind (m_zscan fuel a1 a0 a2) K s) L).
Proof.
  induction fuel as [|fuel IH]; intros a1 a0 a2 md R mm rom s0 s K P L Hp Hag HI H11 H10 H12 HS HK1 HK2.
  { exfalso. clear -HS. cbn [m_zscan MallocTree.mbind mcrash tbind tsafe] in HS. exact HS. }
  pose proof I as HW. note_win HI.
  unfold m_zscan in HS |- *; fold m_zscan in HS |- *. munf. mnorm HS.
  (* [comment removed for export] *)
  mstep Hp HS Hag HI HW. mstep Hp HS Hag HI HW. mstep Hp HS Hag HI HW. mstep Hp HS Hag HI HW.
  all: on_pc 0x98 ltac:(eapply HK1; [ keep_tac | val_tac | val_tac | exact HS ]).
  (* [comment removed for export] *)
  mstep Hp HS Hag HI HW. mstep Hp HS Hag HI HW. mstep Hp HS Hag HI HW.
  all: on_pc 0xd8 ltac:(eapply HK2; [ keep_tac | val_tac | exact HS ]).
  (* [comment removed for export] *)
  eapply (IH a1 (v_addi a0 (-16)) (v_addi a2 (-16)));
    [ exact Hp | exact Hag | exact HI | val_tac | val_tac | val_tac | exact HS | | ].
  - intros a0' a2' R' Hkeep' Ha0 Ha2 HS'. keep_facts Hkeep'.
    eapply HK1; [ keep_tac | exact Ha0 | exact Ha2 | exact HS' ].
  - intros a2' R' Hkeep' Ha2 HS'. keep_facts Hkeep'.
    eapply HK2; [ keep_tac | exact Ha2 | exact HS' ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition MAL0_WL : list Z := [0;1;5;6;7;9;10;11;12;13;14;15;16;17;28;29;30;31]%Z.

Lemma mal0_run {B} : forall fuel (p pp : word) md (R : bvmap 5 word) mm rom (s0 s : mstate) (sp : word)
    (K : word -> M B) (P : B -> mstate -> Prop) (L : B -> mstate -> TSet),
  md_pure md -> magree s mm -> minv s0 s ->
  getr R 8 = p -> getr R 10 = pp -> getr R 2 = v_addi sp (-32) -> getr R 4 = A_TP ->
  bv_unsigned sp mod 16 = 0 ->
  ms_lo s0 <= bv_unsigned sp - CALLOC_D -> bv_unsigned sp <= ms_hi s0 ->
  tsafe (MallocTree.mbind (m_mal0_loop fuel p pp) K s) P ->
  (forall x s' mm' R',
     magree s' mm' -> minv s0 s' ->
     (forall a, ms_lo s0 <= bv_unsigned a < ms_hi s0 -> mm' a = mm a) ->
     (forall r, wreg MAL0_WL r = false -> getr R' r = getr R r) ->
     getr R' 9 = x ->
     tsafe (K x s') P ->
     realizes ml_segs (mkCfg (mkst R' (pc+ PC_CALLOC 0xf0) mm' rom) (with_vmmaps (ms_vm s') md)) (tshape (K x s') L)) ->
  realizes ml_segs (mkCfg (mkst R (pc+ PC_CALLOC 0xb0) mm rom) (with_vmmaps (ms_vm s) md))
           (tshape (MallocTree.mbind (m_mal0_loop fuel p pp) K s) L).
Proof.
  induction fuel as [|fuel IH]; intros p pp md R mm rom s0 s sp K P L Hp Hag HI H8 H10 H2 H4 Hal Hlo Hhi HS HK.
  { exfalso. clear -HS. cbn [m_mal0_loop MallocTree.mbind mcrash tbind tsafe] in HS. exact HS. }
  pose proof I as Hret. pose proof Hlo as HloD. unfold CALLOC_D, ALLOC_STACK in Hlo.
  pose proof HI as HI0. destruct HI0 as (_ & _ & _ & Hlo0 & _ & Hhi64 & _).
  pose proof (mwin_init s0 mm sp 0 ltac:(intros a Ha; lia)) as HW. note_win HI.
  unfold m_mal0_loop in HS |- *; fold m_mal0_loop in HS |- *. unfold MAL0_WL. munf. mnorm HS.
  (* [comment removed for export] *)
  mstep Hp HS Hag HI HW. mstep Hp HS Hag HI HW. mstep Hp HS Hag HI HW.
  lazymatch goal with
  | |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) (tshape (MallocTree.mbind (m_zscan ?f ?a1 ?a0 ?a2) ?Kc ?sb) _) =>
      eapply (zscan_run f a1 a0 a2 md Rc mm rom s0 sb Kc);
        [ exact Hp | exact Hag | exact HI | val_tac | val_tac | val_tac | exact HS | | ]
  end.
  - (* [comment removed for export] *)
    clear HS. intros a0' a2' R' Hkeep' Ha0 Ha2 HS. keep_facts Hkeep'. mnorm HS.
    mrunx_until Hp HS Hag HI HW HK Hret calloc_calls (bv_unsigned PC_CALLOC + 0xa4).
    (* [comment removed for export] *)
    mstepx Hp HS Hag HI HW HK Hret calloc_calls. mstepx Hp HS Hag HI HW HK Hret calloc_calls.
    mstepx Hp HS Hag HI HW HK Hret calloc_calls.
    all: on_pc 0xf0 ltac:(loop_exit HK K Hag HI HS).
    lazymatch goal with
    | |- realizes _ (mkCfg (mkst ?Rc _ ?mc _) _) (tshape (MallocTree.mbind (m_mal0_loop ?f ?p' ?pp') _ ?sb) _) =>
        eapply (IH p' pp' md Rc mc rom s0 sb sp);
          [ exact Hp | exact Hag | exact HI | val_tac | val_tac | val_tac | val_tac | exact Hal | exact HloD | exact Hhi | exact HS | ]
    end.
    clear HS. intros x s' mm' R'' Hag' HI' HJ Hkeep'' Hx HS.
    eapply (HK x s'); [ exact Hag' | exact HI' | | | exact Hx | exact HS ].
    + clear HI; rename HI' into HI; note_win HI. keep_facts Hkeep''. win_same.
    + keep_facts Hkeep''. keep_tac.
  - (* [comment removed for export] *)
    clear HS. intros a2' R' Hkeep' Ha2 HS. keep_facts Hkeep'. mnorm HS.
    mrunx_until Hp HS Hag HI HW HK Hret calloc_calls (bv_unsigned PC_CALLOC + 0xe4).
    mstepx Hp HS Hag HI HW HK Hret calloc_calls. mstepx Hp HS Hag HI HW HK Hret calloc_calls.
    mstepx Hp HS Hag HI HW HK Hret calloc_calls.
    all: on_pc 0xf0 ltac:(loop_exit HK K Hag HI HS).
    lazymatch goal with
    | |- realizes _ (mkCfg (mkst ?Rc _ ?mc _) _) (tshape (MallocTree.mbind (m_mal0_loop ?f ?p' ?pp') _ ?sb) _) =>
        eapply (IH p' pp' md Rc mc rom s0 sb sp);
          [ exact Hp | exact Hag | exact HI | val_tac | val_tac | val_tac | val_tac | exact Hal | exact HloD | exact Hhi | exact HS | ]
    end.
    clear HS. intros x s' mm' R'' Hag' HI' HJ Hkeep'' Hx HS.
    eapply (HK x s'); [ exact Hag' | exact HI' | | | exact Hx | exact HS ].
    + clear HI; rename HI' into HI; note_win HI. keep_facts Hkeep''. win_same.
    + keep_facts Hkeep''. keep_tac.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac calloc_tail Hp HS Hag HI HW HK Hret :=
  idtac;
  mrunx_until Hp HS Hag HI HW HK Hret calloc_calls (bv_unsigned PC_CALLOC + 0x10c);
  mach Hp HS;   (* [comment removed for export] *)
  mach_tailcall Hp HS Hag HI HW HK (memset0_refines (fx:=_)).

Theorem calloc_refines : calloc_stmt.
Proof.
  unfold calloc_stmt.
  intros md regs mm rom s fuel m n sp ret P L Hp Hvm Hag H2 Hal Hlo0 Hlo Hhi Hhi64 Hwt Hstk H1 Hret H4 H10 H11 HS HK.
  unfold CALLOC_D, ALLOC_STACK in *.
  pose proof (minv_init s sp (1024 + 32) Hlo0 Hlo ltac:(lia) Hhi Hhi64 Hwt) as HI.
  pose proof (mwin_init s mm sp (1024 + 32) Hstk) as HW.
  rewrite <- (with_vmmaps_same md), <- Hvm. note_win HI.
  unfold m_calloc in HS |- *. munf. mnorm HS.
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret calloc_calls (bv_unsigned PC_CALLOC + 0x10). mark_frame 32.
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret calloc_calls (bv_unsigned PC_CALLOC + 0x50).
  (* [comment removed for export] *)
  all: mrunx_until Hp HS Hag HI HW HK Hret calloc_calls (bv_unsigned PC_CALLOC + 0x60).
  (* [comment removed for export] *)
  all: mrunx_until Hp HS Hag HI HW HK Hret calloc_calls (bv_unsigned PC_CALLOC + 0x64).
  (* [comment removed for export] *)
  all: mstepx Hp HS Hag HI HW HK Hret calloc_calls.
  all: mstepx Hp HS Hag HI HW HK Hret calloc_calls.
  all: on_pc 0xf0 ltac:(calloc_tail Hp HS Hag HI HW HK Hret).
  (* [comment removed for export] *)
  all: mrunx_until Hp HS Hag HI HW HK Hret calloc_calls (bv_unsigned PC_CALLOC + 0x88).
  all: mstepx Hp HS Hag HI HW HK Hret calloc_calls.
  all: mstepx Hp HS Hag HI HW HK Hret calloc_calls.
  all: mstepx Hp HS Hag HI HW HK Hret calloc_calls.
  all: on_pc 0x94 ltac:(idtac; mstepx Hp HS Hag HI HW HK Hret calloc_calls).
  all: on_pc 0xf0 ltac:(calloc_tail Hp HS Hag HI HW HK Hret).
  (* [comment removed for export] *)
  all: lazymatch goal with
    | |- realizes _ (mkCfg (mkst ?Rc _ ?mc ?rom) (with_vmmaps _ ?md)) (tshape (MallocTree.mbind (m_mal0_loop ?f ?p' ?pp') ?Kc ?sb) _) =>
        eapply (mal0_run f p' pp' md Rc mc rom s sb sp Kc);
          [ exact Hp | exact Hag | exact HI | val_tac | val_tac | val_tac | val_tac | exact Hal
          | cbn [ms_lo ms_hi ms_mem ms_vm upd]; unfold CALLOC_D, ALLOC_STACK; alia
          | cbn [ms_lo ms_hi ms_mem ms_vm upd]; alia
          | exact HS | ]
    end.
  all: clear HS; intros x s' mm' R' Hag' HI' HJ Hkeep Hx HS;
       clear Hag HI; rename Hag' into Hag; rename HI' into HI; note_win HI;
       frame_facts HW mm'; keep_facts Hkeep; mnorm HS.
  all: calloc_tail Hp HS Hag HI HW HK Hret.
Qed.
End Calloc.
