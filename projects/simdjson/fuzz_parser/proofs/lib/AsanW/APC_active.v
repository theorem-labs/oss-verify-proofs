(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AU_kit AU_iface AHarnessU_iface AU_client_kit AU_fuzz_kit AU_parts_iface AU_steptac.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import ShadowTac APC_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_tight | solve_load_image ].
Local Ltac solve_store ::= solve_store_tight.

Section CANSEC1. Context {rc : runConstT}.
Definition AGET_ACTIVE : Z := 0x9735c.
Definition AACTIVE_STACK : Z := 32.       (* [comment removed for export] *)

Definition aactive_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 AACTIVE) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ munch ((lo, bv_unsigned sp) :: client_wr) m m' /\ wmono asegs m m'
    /\ client_static1 m'.

Definition aactive_stmt : Prop :=
  forall (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - AACTIVE_STACK -> bv_unsigned sp <= 2^47 ->
  mem_inv asegs m ->
  client_static0 m \/ client_static1 m ->
  rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG ->
  evtF asegs RNG (aactive_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AGET_ACTIVE) fc None m (seg_rom asegs)).

Theorem aactive_proof : aactive_stmt.
Proof.
  unfold aactive_stmt. intros until lo. intros ST LOA LOS SPT MI CS RSTK RI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold AACTIVE_STACK in LOS. atop_facts. unfold AGET_ACTIVE.
  pose proof (munch_refl ((lo, bv_unsigned sp) :: client_wr) m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold client_wr in MU.
  carve_frame 16%nat ST.
  destruct CS as [IMG|BLT].
  - (* [comment removed for export] *)
    destruct IMG as (CA & CG & CF & CFG). unfold AACTIVE, AACTIVE_GUARD, AFALLBACK, AFALLBACK_GUARD, guard0, w0 in *.
    steps_to 0xc0844.
    carve_frame 16%nat ST.
    steps_to 0x9738c.
    zstep.
    release_frame FR0 ST (bv_unsigned sp + -16). release_frame FR ST (bv_unsigned sp).
    apply evtF_done. unfold aactive_post. do 14 eexists. eexists. split; [reflexivity|].
    split; [exact MI|]. split; [exact ST|]. split; [unfold client_wr; exact MU|]. split; [exact WM|].
    unfold client_static1, guard1, fallback_cells, AACTIVE, AACTIVE_GUARD, AFALLBACK, AFALLBACK_GUARD, AFALLBACK_VT, AFALLBACK_NAME, AFALLBACK_DESC, w0.
    split; [exact CA|]. split; [exact CG|]. split; [exact CF| exact CFG].
  - (* [comment removed for export] *)
    pose proof BLT as (CA & CG & CF & CFG).
    unfold AACTIVE, AACTIVE_GUARD, AFALLBACK, AFALLBACK_GUARD, guard1, fallback_cells, AFALLBACK_VT, AFALLBACK_NAME, AFALLBACK_DESC, w0 in *.
    steps_to 0x9738c.
    zstep.
    release_frame FR ST (bv_unsigned sp).
    apply evtF_done. unfold aactive_post. do 14 eexists. eexists. split; [reflexivity|].
    split; [exact MI|]. split; [exact ST|]. split; [unfold client_wr; exact MU|]. split; [exact WM|].
    unfold client_static1, guard1, fallback_cells, AACTIVE, AACTIVE_GUARD, AFALLBACK, AFALLBACK_GUARD, AFALLBACK_VT, AFALLBACK_NAME, AFALLBACK_DESC, w0.
    split; [exact CA|]. split; [exact CG|]. split; [exact CF| exact CFG].
Qed.
End CANSEC1.
