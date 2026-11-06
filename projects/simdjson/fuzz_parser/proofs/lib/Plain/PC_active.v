(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import Stdio_pure Printf_pieces.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PImg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface ROpNew ROpNew_nt.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require RMalloc_ifaceP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad Stdio Malloc HarnessP ProgP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PC_kit PU_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.
Definition PGET_ACTIVE : Z := 0x27b94.
Definition ACTIVE_STACK : Z := 64.       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition active_W (lo SP : Z) : list (Z * Z) := (lo, SP) :: client_wr.

Definition active_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 PACTIVE) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp)
    /\ munch (active_W lo (bv_unsigned sp)) m m' /\ wmono psegs m m'
    /\ cstat_built m'.

Definition active_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk psegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - ACTIVE_STACK ->
  mem_inv psegs m ->
  cstat_image m \/ cstat_built m ->
  evt psegs (active_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PGET_ACTIVE) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cstat_image_cells : forall m, cstat_image m ->
  rw_cells psegs m PACTIVE [C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells psegs m PFALLBACK_GUARD [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells psegs m PFALLBACK [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].
Proof.
  intros m IMG. unfold cstat_image in IMG. unfold PACTIVE, PFALLBACK_GUARD, PFALLBACK.
  split; [|split].
  - apply (InitMem.rw_cells_recast psegs m _ [CB 10 (repeat (Z_to_bv 8 0) 10)]);
      [ apply (InitMem.rw_cells_image0 psegs m _ (repeat (Z_to_bv 8 0) 10));
        [ intros a Ha; apply IMG; cbn [length repeat] in Ha; lia | vm_compute; reflexivity | lia | cbn [length repeat]; lia ]
      | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ].
  - apply (InitMem.rw_cells_recast psegs m _ [CB 2 (repeat (Z_to_bv 8 0) 2)]);
      [ apply (InitMem.rw_cells_image0 psegs m _ (repeat (Z_to_bv 8 0) 2));
        [ intros a Ha; apply IMG; cbn [length repeat] in Ha; lia | vm_compute; reflexivity | lia | cbn [length repeat]; lia ]
      | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ].
  - apply (InitMem.rw_cells_recast psegs m _ [CB 44 (repeat (Z_to_bv 8 0) 44)]);
      [ apply (InitMem.rw_cells_image0 psegs m _ (repeat (Z_to_bv 8 0) 44));
        [ intros a Ha; apply IMG; cbn [length repeat] in Ha; lia | vm_compute; reflexivity | lia | cbn [length repeat]; lia ]
      | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lit_if := lazymatch goal with |- evt _ _ (MS ?R ?F (if ?c then ?x else ?y) ?fc ?rv ?mm ?ro) =>
   let v := eval vm_compute in c in
   lazymatch v with true => change (if c then x else y) with x | false => change (if c then x else y) with y end end.
(* [comment removed for export] *)
Ltac run_to X := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 X) _ _ _ _) => fail | _ => first [lit_if | zstep] end).

Theorem active_proof : active_stmt.
Proof.
  unfold active_stmt. intros until lo. intros ST LOA LOS MI CS.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold ACTIVE_STACK in LOS. atop_facts. unfold PGET_ACTIVE.
  pose proof (munch_refl (active_W lo (bv_unsigned sp)) m) as MU. pose proof (wmono_refl psegs m) as WM.
  unfold active_W, client_wr in MU.
  carve_frame 32%nat ST.
  destruct CS as [IMG|BLT].
  - (* [comment removed for export] *)
    destruct (cstat_image_cells m IMG) as (CA & CG & CF). clear IMG. unfold PACTIVE, PFALLBACK_GUARD, PFALLBACK in *.
    run_to 0x3860c.
    carve_frame 32%nat ST.
    run_to 0x27c0c.
    zstep.
    release_frame FR0 ST (bv_unsigned sp + -32). release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold active_post. do 14 eexists. eexists. split; [reflexivity|].
    split; [exact MI|]. split; [exact ST|]. split; [unfold active_W, client_wr; exact MU|]. split; [exact WM|].
    destruct (rw_cells_app_split psegs _ 553368 [C8 (Z_to_bv 64 553488)] [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)] CA) as [CA1 CA2].
    change (553368 + Z.of_nat (cells_size [C8 (Z_to_bv 64 553488)])) with 553376 in CA2.
    unfold cstat_built, guard1, fallback_cells, PACTIVE, PACTIVE_GUARD, PFALLBACK, PFALLBACK_GUARD, PFALLBACK_VT, PFALLBACK_NAME, PFALLBACK_DESC, w0.
    split; [exact CA1|]. split; [exact CA2|]. split; [exact CF| exact CG].
  - (* [comment removed for export] *)
    pose proof BLT as (CA & CG & CF & CFG). unfold PACTIVE, PACTIVE_GUARD, PFALLBACK, PFALLBACK_GUARD, guard1, fallback_cells in *.
    run_to 0x27bcc.
    zstep.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold active_post. do 14 eexists. eexists. split; [reflexivity|].
    split; [exact MI|]. split; [exact ST|]. split; [unfold active_W, client_wr; exact MU|]. split; [exact WM|].
    unfold cstat_built, guard1, fallback_cells, PACTIVE, PACTIVE_GUARD, PFALLBACK, PFALLBACK_GUARD.
    split; [exact CA|]. split; [exact CG|]. split; [exact CF| exact CFG].
Qed.
End CANSEC1.
