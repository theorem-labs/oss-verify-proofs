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
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require Import RRef_syswrap RRef_enframe RRef_ameta RRef_loops RRef_aslot1 RRef_aslot2 RRef_aslot3.
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

Section Pieces6.
Context {fx : FPState} {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL}.
#[local] Existing Instance reloc_layout.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac use_mm2 sp DD Hp Hag HI HW HS HK K :=
  use_piece2 as_mm2_piece sp DD Hp Hag HI HW HS;
  let x := fresh "x" in let HX := fresh "HX" in
  intros x HX HS; mnorm HS; piece_exit HK K Hag HI HS.

Lemma as_mmapg_piece {B} : forall md (R : bvmap 5 word) mm rom (s0 s : mstate) (sp : word) (DD : Z)
    (s7 pm sc req m size usage pg cnt1 a4 : word)
    (K : word -> M B) (P : B -> mstate -> Prop) (L : B -> mstate -> TSet),
  md_pure md -> magree s mm -> minv s0 s ->
  getr R 2 = v_addi sp (-144) -> getr R 4 = A_TP ->
  getr R 23 = s7 -> getr R 21 = pm -> getr R 8 = sc -> getr R 18 = req -> getr R 9 = m ->
  getr R 24 = size -> getr R 10 = usage -> getr R 11 = pg -> getr R 19 = cnt1 -> getr R 14 = a4 ->
  getr R 12 = v_addi size 16 -> getr R 22 = A_LOCK ->
  bv_unsigned sp mod 16 = 0 -> 224 <= DD ->
  ms_lo s0 <= bv_unsigned sp - DD -> bv_unsigned sp <= ms_hi s0 ->
  (forall a, bv_unsigned sp - DD <= bv_unsigned a < bv_unsigned sp -> mm a <> None) ->
  tsafe (MallocTree.mbind (as_mmapg s7 pm sc req m size usage pg cnt1 a4) K s) P ->
  (forall x s' mm' R',
     magree s' mm' -> minv s0 s' ->
     (forall a, ms_lo s0 <= bv_unsigned a < ms_hi s0 ->
                ~ (bv_unsigned sp - DD <= bv_unsigned a < bv_unsigned sp - 96) -> mm' a = mm a) ->
     (forall a, bv_unsigned sp - DD <= bv_unsigned a < bv_unsigned sp - 96 -> mm' a <> None) ->
     (forall r, wreg MM2_WL r = false -> getr R' r = getr R r) ->
     getr R' 10 = x ->
     tsafe (K x s') P ->
     realizes ml_segs (mkCfg (mkst R' (pc+ PC_ALLOC_SLOT 0x860) mm' rom) (with_vmmaps (ms_vm s') md)) (tshape (K x s') L)) ->
  realizes ml_segs (mkCfg (mkst R (pc+ PC_ALLOC_SLOT 0x2cc) mm rom) (with_vmmaps (ms_vm s) md))
           (tshape (MallocTree.mbind (as_mmapg s7 pm sc req m size usage pg cnt1 a4) K s) L).
Proof.
  intros md R mm rom s0 s sp DD s7 pm sc req m size usage pg cnt1 a4 K P L
         Hp Hag HI H2 H4 H23 H21 H8 H18 H9 H24 H10 H11 H19 H14 H12 H22
         Hal HDD Hlo Hhi Hstk HS HK.
  pose proof I as Hret. note_win HI. sys_hyps.
  pose proof HI as HI0. destruct HI0 as (_ & _ & _ & Hlo0 & _ & Hhi64 & _).
  pose proof (mwin_init s0 mm sp DD Hstk) as HW.
  unfold as_mmapg, as_bn, MM2_WL in HS |- *. munf. lits64 HS. mnorm HS.
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x2d4).
  mstepx Hp HS Hag HI HW HK Hret as_calls.
  all: let tq := rl_name_of (bv_unsigned PC_ALLOC_SLOT + 0x3ac)%Z in cur_pc ltac:(fun u => tryif constr_eq u tq then
         (mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x580); use_mm2 sp DD Hp Hag HI HW HS HK K)
         else idtac).
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x2ec).
  mstepx Hp HS Hag HI HW HK Hret as_calls.
  all: let tq := rl_name_of (bv_unsigned PC_ALLOC_SLOT + 0x57c)%Z in cur_pc ltac:(fun u => tryif constr_eq u tq then
         (mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x580); use_mm2 sp DD Hp Hag HI HW HS HK K)
         else idtac).
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x2fc).
  mstepx Hp HS Hag HI HW HK Hret as_calls.
  all: let tq := rl_name_of (bv_unsigned PC_ALLOC_SLOT + 0x580)%Z in cur_pc ltac:(fun u => tryif constr_eq u tq then
         (mach_pload HS; use_mm2 sp DD Hp Hag HI HW HS HK K)
         else idtac).
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x304).
  mstepx Hp HS Hag HI HW HK Hret as_calls.
  all: mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x580).
  all: use_mm2 sp DD Hp Hag HI HW HS HK K.
Qed.

End Pieces6.


Lemma cnt1_bound : forall (cnt h q : word), bv_unsigned cnt < 256 ->
  bv_unsigned (if c_eq cnt (Z_to_bv 64 1) then v_subw (Z_to_bv 64 2) (v_sltu h q) else cnt) < 256.
Proof.
  intros cnt h q Hc. destruct (c_eq cnt (Z_to_bv 64 1)); [|exact Hc].
  unfold v_subw, v_sltu. destruct (c_ltu h q); vm_compute; reflexivity.
Qed.

Ltac xr_extra ::= first [ apply u_lbu | apply cnt_bound; assumption | apply cnt1_bound; assumption ].

Section Pieces7.
Context {fx : FPState} {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL}.
#[local] Existing Instance reloc_layout.

Definition RES_WL : list Z := [0;1;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;21;22;24;25;28;29;30;31]%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma as_group_piece {B} : forall (fuel' : nat) md (R : bvmap 5 word) mm rom (s0 s : mstate)
    (sp s7 sc req : word)
    (K : word -> M B) (P : B -> mstate -> Prop) (L : B -> mstate -> TSet),
  aslot_at fuel' ->
  md_pure md -> magree s mm -> minv s0 s ->
  getr R 2 = v_addi sp (-144) -> getr R 4 = A_TP ->
  getr R 23 = s7 -> getr R 21 = at_ s7 88 -> getr R 8 = sc -> getr R 18 = req ->
  getr R 22 = A_LOCK ->
  bv_unsigned sp mod 16 = 0 ->
  ms_lo s0 <= bv_unsigned sp - (alloc_slot_D fuel' + 144) -> bv_unsigned sp <= ms_hi s0 ->
  (forall a, bv_unsigned sp - (alloc_slot_D fuel' + 144) <= bv_unsigned a < bv_unsigned sp -> mm a <> None) ->
  tsafe (MallocTree.mbind (as_group fuel' (at_ sp (-144)) s7 (at_ s7 88) sc req) K s) P ->
  (forall x s' mm' R',
     magree s' mm' -> minv s0 s' ->
     (forall a, ms_lo s0 <= bv_unsigned a < ms_hi s0 ->
                ~ (bv_unsigned sp - (alloc_slot_D fuel' + 144) <= bv_unsigned a < bv_unsigned sp - 96) -> mm' a = mm a) ->
     (forall a, bv_unsigned sp - (alloc_slot_D fuel' + 144) <= bv_unsigned a < bv_unsigned sp - 96 -> mm' a <> None) ->
     (forall r, wreg RES_WL r = false -> getr R' r = getr R r) ->
     getr R' 10 = x ->
     tsafe (K x s') P ->
     realizes ml_segs (mkCfg (mkst R' (pc+ PC_ALLOC_SLOT 0x860) mm' rom) (with_vmmaps (ms_vm s') md)) (tshape (K x s') L)) ->
  realizes ml_segs (mkCfg (mkst R (pc+ PC_ALLOC_SLOT 0x1e0) mm rom) (with_vmmaps (ms_vm s) md))
           (tshape (MallocTree.mbind (as_group fuel' (at_ sp (-144)) s7 (at_ s7 88) sc req) K s) L).
Proof.
  intros fuel' md R mm rom s0 s sp s7 sc req K P L REC Hp Hag HI H2 H4 H23 H21 H8 H18 H22
         Hal Hlo Hhi Hstk HS HK.
  pose proof I as Hret. note_win HI. sys_hyps.
  pose proof HI as HI0. destruct HI0 as (_ & _ & _ & Hlo0 & _ & Hhi64 & _).
  pose proof (alloc_slot_D_ge fuel') as HDge.
  pose proof (mwin_init s0 mm sp (alloc_slot_D fuel' + 144) Hstk) as HW.
  unfold as_group, RES_WL in HS |- *. munf. lits64 HS. mnorm HS.
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x200).
  mstepx Hp HS Hag HI HW HK Hret as_calls.
  all: piece_exit_at (bv_unsigned PC_ALLOC_SLOT + 0x860) HK K Hag HI HS.
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x218).
  use_piece as_cnt_piece Hp Hag HI HW HS.
  intros cnt [HXc Hcb] HS. mnorm HS.
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x2b0).
  mach_vlet (bv_unsigned PC_ALLOC_SLOT + 0x2c0) [14;15;19]%Z
    (fun (e : word) (R' : bvmap 5 word) => getr R' 19 = e /\ bv_unsigned e < 256) as CUT1 HS.
  { mach_pure Hp HS (bv_unsigned PC_ALLOC_SLOT + 0x2c0). all: use_vcut CUT1. }
  intros cnt1 [HX1 Hcb1] HS.
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x2c8).
  mstepx Hp HS Hag HI HW HK Hret as_calls.
  all: let tq := rl_name_of (bv_unsigned PC_ALLOC_SLOT + 0x310)%Z in cur_pc ltac:(fun u => tryif constr_eq u tq then
         use_piece (as_nested_piece fuel') Hp Hag HI HW HS
       else use_piece2 as_mmapg_piece sp (alloc_slot_D fuel' + 144) Hp Hag HI HW HS).
  all: intros x HX HS; mnorm HS; piece_exit HK K Hag HI HS.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma as_res_piece {B} : forall (fuel' : nat) md (R : bvmap 5 word) mm rom (s0 s : mstate)
    (sp s7 sc req : word)
    (K : word -> M B) (P : B -> mstate -> Prop) (L : B -> mstate -> TSet),
  aslot_at fuel' ->
  md_pure md -> magree s mm -> minv s0 s ->
  getr R 2 = v_addi sp (-144) -> getr R 4 = A_TP ->
  getr R 23 = s7 -> getr R 8 = sc -> getr R 18 = req ->
  getr R 22 = A_LOCK ->
  bv_unsigned sp mod 16 = 0 ->
  ms_lo s0 <= bv_unsigned sp - (alloc_slot_D fuel' + 144) -> bv_unsigned sp <= ms_hi s0 ->
  (forall a, bv_unsigned sp - (alloc_slot_D fuel' + 144) <= bv_unsigned a < bv_unsigned sp -> mm a <> None) ->
  tsafe (MallocTree.mbind (as_res fuel' (at_ sp (-144)) s7 (at_ s7 88) sc req) K s) P ->
  (forall x s' mm' R',
     magree s' mm' -> minv s0 s' ->
     (forall a, ms_lo s0 <= bv_unsigned a < ms_hi s0 ->
                ~ (bv_unsigned sp - (alloc_slot_D fuel' + 144) <= bv_unsigned a < bv_unsigned sp - 96) -> mm' a = mm a) ->
     (forall a, bv_unsigned sp - (alloc_slot_D fuel' + 144) <= bv_unsigned a < bv_unsigned sp - 96 -> mm' a <> None) ->
     (forall r, wreg RES_WL r = false -> getr R' r = getr R r) ->
     getr R' 10 = x ->
     tsafe (K x s') P ->
     realizes ml_segs (mkCfg (mkst R' (pc+ PC_ALLOC_SLOT 0x860) mm' rom) (with_vmmaps (ms_vm s') md)) (tshape (K x s') L)) ->
  realizes ml_segs (mkCfg (mkst R (pc+ PC_ALLOC_SLOT 0x58) mm rom) (with_vmmaps (ms_vm s) md))
           (tshape (MallocTree.mbind (as_res fuel' (at_ sp (-144)) s7 (at_ s7 88) sc req) K s) L).
Proof.
  intros fuel' md R mm rom s0 s sp s7 sc req K P L REC Hp Hag HI H2 H4 H23 H8 H18 H22
         Hal Hlo Hhi Hstk HS HK.
  pose proof I as Hret. note_win HI. sys_hyps.
  pose proof HI as HI0. destruct HI0 as (_ & _ & _ & Hlo0 & _ & Hhi64 & _).
  pose proof (alloc_slot_D_ge fuel') as HDge.
  pose proof (mwin_init s0 mm sp (alloc_slot_D fuel' + 144) Hstk) as HW.
  unfold as_res, RES_WL in HS |- *. munf. lits64 HS. mnorm HS.
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x60).
  use_piece as_tav_piece Hp Hag HI HW HS.
  intros [[m mask]|] HX HS.
  - (* [comment removed for export] *)
    destruct HX as [HXm HXk]. cbn [as_tav_pc] in *. unfold as_take in HS |- *. munf. mnorm HS.
    mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x1b0).
    mstepx Hp HS Hag HI HW HK Hret as_calls.
    all: let tq := rl_name_of (bv_unsigned PC_ALLOC_SLOT + 0x1e0)%Z in cur_pc ltac:(fun u => tryif constr_eq u tq then model_crash HS else idtac).
    as_run Hp HS Hag HI HW HK Hret K (fun _ : word => (pc+ PC_ALLOC_SLOT 0x860)).
    piece_exit HK K Hag HI HS.
  - (* [comment removed for export] *)
    cbn [as_tav_pc] in *. mnorm HS.
    use_piece (as_group_piece fuel') Hp Hag HI HW HS.
    intros x HX' HS. mnorm HS. piece_exit HK K Hag HI HS.
Qed.


End Pieces7.
