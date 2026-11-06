(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import decidable.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes
  PureModel VmLedger AllocIface AsanCeil AgentLib.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocShape RefLrSc RefStep RefStmts RefSys RefPieces RefStep3.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import RRef_syswrap RRef_enframe RRef_ameta RRef_loops.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import RefStepR.
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

(* [comment removed for export] *)
Ltac as_run Hp HS Hag HI HW HK Hret K PCF :=
  repeat (progress (mrun_to_k Hp HS Hag HI HW HK Hret as_calls K PCF)).

(* [comment removed for export] *)
Ltac piece_exit_k HK K Hag HI HS := pc_lit; use_cut_k HK K Hag HI HS.

(* [comment removed for export] *)
Ltac piece_exit_k_at pcZ HK K Hag HI HS :=
  let pcZ := rl_name_of pcZ in
  cur_pc ltac:(fun u => tryif constr_eq u pcZ then piece_exit_k HK K Hag HI HS else idtac).
Ltac piece_exit_at pcZ HK K Hag HI HS :=
  let pcZ := rl_name_of pcZ in
  cur_pc ltac:(fun u => tryif constr_eq u pcZ then piece_exit HK K Hag HI HS else idtac).
Ltac use_cut_k_at pcZ CUT Kx Hag HI HS :=
  let pcZ := rl_name_of pcZ in
  cur_pc ltac:(fun u => tryif constr_eq u pcZ then use_cut_k CUT Kx Hag HI HS else idtac).
Ltac use_cut_kx_at pcZ CUT Kx Hag HI HS :=
  let pcZ := rl_name_of pcZ in
  cur_pc ltac:(fun u => tryif constr_eq u pcZ then use_cut_kx CUT Kx Hag HI HS else idtac).
Ltac run_exit_k_not_at pcZ Hp HS Hag HI HW HK Hret K PCF :=
  let pcZ := rl_name_of pcZ in
  cur_pc ltac:(fun u => tryif constr_eq u pcZ then idtac
                        else (as_run Hp HS Hag HI HW HK Hret K PCF; piece_exit_k HK K Hag HI HS)).
Ltac run_exit_not_at pcZ Hp HS Hag HI HW HK Hret K PCF :=
  let pcZ := rl_name_of pcZ in
  cur_pc ltac:(fun u => tryif constr_eq u pcZ then idtac
                        else (as_run Hp HS Hag HI HW HK Hret K PCF; piece_exit HK K Hag HI HS)).
Ltac run_cut_k_not_at pcZ Hp HS Hag HI HW HK Hret CUT Kx PCF :=
  let pcZ := rl_name_of pcZ in
  cur_pc ltac:(fun u => tryif constr_eq u pcZ then idtac
                        else (as_run Hp HS Hag HI HW HK Hret Kx PCF; use_cut_k CUT Kx Hag HI HS)).
Ltac run_cut_kx_not_at pcZ Hp HS Hag HI HW HK Hret CUT Kx PCF :=
  let pcZ := rl_name_of pcZ in
  cur_pc ltac:(fun u => tryif constr_eq u pcZ then idtac
                        else (as_run Hp HS Hag HI HW HK Hret Kx PCF; use_cut_kx CUT Kx Hag HI HS)).

Section Pieces1.
Context {fx : FPState} {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL}.
#[local] Existing Instance reloc_layout.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma as_tail_piece {B} : forall md (R : bvmap 5 word) mm rom (s0 s : mstate) (s7 pm sc m p cnt aidx c1 : word)
    (K : word -> M B) (P : B -> mstate -> Prop) (L : B -> mstate -> TSet),
  md_pure md -> magree s mm -> minv s0 s ->
  getr R 23 = s7 -> getr R 21 = pm -> getr R 8 = sc -> getr R 9 = m -> getr R 10 = p ->
  getr R 25 = cnt -> getr R 12 = aidx -> getr R 11 = c1 ->
  tsafe (MallocTree.mbind (as_tail s7 pm sc m p cnt aidx c1) K s) P ->
  (forall x s' mm' R',
     magree s' mm' -> minv s0 s' ->
     (forall a, ms_lo s0 <= bv_unsigned a < ms_hi s0 -> mm' a = mm a) ->
     (forall r, wreg [8;10;11;12;13;14;21]%Z r = false -> getr R' r = getr R r) ->
     getr R' 10 = x ->
     tsafe (K x s') P ->
     realizes ml_segs (mkCfg (mkst R' (pc+ PC_ALLOC_SLOT 0x860) mm' rom) (with_vmmaps (ms_vm s') md)) (tshape (K x s') L)) ->
  realizes ml_segs (mkCfg (mkst R (pc+ PC_ALLOC_SLOT 0x708) mm rom) (with_vmmaps (ms_vm s) md))
           (tshape (MallocTree.mbind (as_tail s7 pm sc m p cnt aidx c1) K s) L).
Proof.
  intros md R mm rom s0 s s7 pm sc m p cnt aidx c1 K P L Hp Hag HI H23 H21 H8 H9 H10 H25 H12 H11 HS HK.
  pose proof I as HW. pose proof I as Hret. note_win HI. sys_hyps.
  unfold as_tail in HS |- *. munf. mnorm HS.
  as_run Hp HS Hag HI HW HK Hret K (fun _ : word => (pc+ PC_ALLOC_SLOT 0x860)).
  all: piece_exit_k HK K Hag HI HS.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition as_fail_stmt (ENTRY : word) : Prop :=
  forall B md (R : bvmap 5 word) mm rom (s0 s : mstate) (sp : word) (DD : Z) (m : word)
    (K : word -> M B) (P : B -> mstate -> Prop) (L : B -> mstate -> TSet),
  md_pure md -> magree s mm -> minv s0 s ->
  getr R 2 = v_addi sp (-144) -> getr R 9 = m -> getr R 22 = A_LOCK ->
  ms_lo s0 <= bv_unsigned sp - DD -> bv_unsigned sp <= ms_hi s0 -> 144 <= DD ->
  (forall a, bv_unsigned sp - DD <= bv_unsigned a < bv_unsigned sp -> mm a <> None) ->
  tsafe (MallocTree.mbind (as_fail m) K s) P ->
  (forall x s' mm' R',
     magree s' mm' -> minv s0 s' ->
     (forall a, ms_lo s0 <= bv_unsigned a < ms_hi s0 ->
                ~ (bv_unsigned sp - DD <= bv_unsigned a < bv_unsigned sp - 96) -> mm' a = mm a) ->
     (forall a, bv_unsigned sp - DD <= bv_unsigned a < bv_unsigned sp - 96 -> mm' a <> None) ->
     (forall r, wreg [10;11;22]%Z r = false -> getr R' r = getr R r) ->
     getr R' 10 = x ->
     tsafe (K x s') P ->
     realizes ml_segs (mkCfg (mkst R' (pc+ PC_ALLOC_SLOT 0x860) mm' rom) (with_vmmaps (ms_vm s') md)) (tshape (K x s') L)) ->
  realizes ml_segs (mkCfg (mkst R ENTRY mm rom) (with_vmmaps (ms_vm s) md))
           (tshape (MallocTree.mbind (as_fail m) K s) L).

Ltac as_fail_tac :=
  intros B md R mm rom s0 s sp DD m K P L Hp Hag HI H2 H9 H22 Hlo Hhi HDD Hstk HS HK;
  pose proof I as Hret; note_win HI; sys_hyps;
  pose proof HI as HI0; destruct HI0 as (_ & _ & _ & Hlo0 & _ & Hhi64 & _);
  pose proof (mwin_init s0 mm sp DD Hstk) as HW;
  unfold as_fail, m_free_meta_ag in HS |- *; munf; mnorm HS;
  as_run Hp HS Hag HI HW HK Hret K (fun _ : word => (pc+ PC_ALLOC_SLOT 0x860)).

Lemma as_fail_piece1 : as_fail_stmt (pc+ PC_ALLOC_SLOT 0x458).
Proof. as_fail_tac. all: piece_exit HK K Hag HI HS. Qed.

Lemma as_fail_piece2 : as_fail_stmt (pc+ PC_ALLOC_SLOT 0x7d8).
Proof. as_fail_tac. all: piece_exit HK K Hag HI HS. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition as_actg_xr (x : option (word * word)) (R' : bvmap 5 word) : Prop :=
  match x with Some (a, b) => getr R' 10 = a /\ getr R' 11 = b | None => False end.

Lemma as_actg_piece {B} : forall md (R : bvmap 5 word) mm rom (s0 s : mstate) (m3 : word)
    (K : option (word * word) -> M B) (P : B -> mstate -> Prop) (L : B -> mstate -> TSet),
  md_pure md -> magree s mm -> minv s0 s ->
  getr R 10 = m3 -> getr R 22 = A_LOCK ->
  tsafe (MallocTree.mbind (as_actg m3) K s) P ->
  (forall x s' mm' R',
     magree s' mm' -> minv s0 s' ->
     (forall a, ms_lo s0 <= bv_unsigned a < ms_hi s0 -> mm' a = mm a) ->
     (forall r, wreg [11;12;13;14;15;16;17]%Z r = false -> getr R' r = getr R r) ->
     as_actg_xr x R' ->
     tsafe (K x s') P ->
     realizes ml_segs (mkCfg (mkst R' (pc+ PC_ALLOC_SLOT 0x1a0) mm' rom) (with_vmmaps (ms_vm s') md)) (tshape (K x s') L)) ->
  realizes ml_segs (mkCfg (mkst R (pc+ PC_ALLOC_SLOT 0x128) mm rom) (with_vmmaps (ms_vm s) md))
           (tshape (MallocTree.mbind (as_actg m3) K s) L).
Proof.
  intros md R mm rom s0 s m3 K P L Hp Hag HI H10 H22 HS HK.
  pose proof I as HW. pose proof I as Hret. note_win HI. sys_hyps.
  unfold as_actg, as_actg_xr in HS |- *. munf. mnorm HS.
  as_run Hp HS Hag HI HW HK Hret K (fun _ : option (word * word) => (pc+ PC_ALLOC_SLOT 0x1a0)).
  all: piece_exit_k HK K Hag HI HS.
Qed.

End Pieces1.
