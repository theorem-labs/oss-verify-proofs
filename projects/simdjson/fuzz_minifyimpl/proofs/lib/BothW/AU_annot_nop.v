(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg RtCells ABase F_apoison F_annot.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import AU_steptac.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import ShadowTac.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_tight | solve_load_image ].
Local Ltac solve_store ::= solve_store_tight.

Ltac bt := let K := fresh "K" in if_cases K; zify_cond K; [| exfalso; rewrite ?unsigned_lit in K by lia; lia].
Ltac bf := let K := fresh "K" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|].

Section CANSEC1. Context {rc : runConstT}.
Definition ANNOT_NOP_STACK : Z := 2128.   (* [comment removed for export] *)

Definition annot_nop_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - ANNOT_NOP_STACK, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma annot_nop_spec : forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (lo A : Z),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> KHIGH <= lo -> lo <= bv_unsigned sp - ANNOT_NOP_STACK ->
  poison_cells m -> annot_cells m ->
  0 <= A -> A + 8 < 2^47 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (annot_nop_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 (A + 8)) (Z_to_bv 64 (A + 8)) (Z_to_bv 64 (A + 8)) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 AANNOT) fc None m (seg_rom bsegs)).
Proof.
  intros until A. intros MI ST KLO LOS (PC1 & _) (AC1 & AC2 & AC3) A0 AT RI RSTK. unfold AANNOT, ANNOT_NOP_STACK, KHIGH in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 2128, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. carve_frame 56%nat ST.
  steps_to 0x84c1c.
  zstep. bt. (* [comment removed for export] *)
  zstep. bf. zstep. bf. zstep. bf. (* [comment removed for export] *)
  steps_to 0x84cd4. zstep. bf. (* [comment removed for export] *)
  zstep. bt. (* [comment removed for export] *)
  steps_to 0x84e48.
  release_frame FR0 ST (bv_unsigned sp).
  zstep. zstep. (* [comment removed for export] *)
  apply evtF_done. unfold annot_nop_post. do 16 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ST].
Qed.
End CANSEC1.
