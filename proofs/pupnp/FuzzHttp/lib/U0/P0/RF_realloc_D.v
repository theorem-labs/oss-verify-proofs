(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs ImgFacts.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import F_malloc_free F_malloc_fast.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import RMallocRep RMallocTree RF_realloc_A.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma rrgen_tomalloc : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x19cf8) sp gp tp t0 t1 t2 a1 a0 a1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19ce8) fc None m (seg_rom rsegs)).
Proof. intros. step. step. step. step. apply evt_done. reflexivity. Qed.

Lemma rrgen_fail : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (ra0 q0 q1 q2 q3 q4 q5 q6 : word) F fc (m : mem) (lo : Z),
  rw_cells rsegs m (bv_unsigned sp + -64) (rr_frame q6 q5 q4 q3 q2 q1 q0 ra0) ->
  stk rsegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - 64 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 q0 q1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 q2 q3 q4 q5 q6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra0) fc None m (seg_rom rsegs) /\ stk rsegs m lo (bv_unsigned sp))
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19cf8) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros FR ST LO MI. unfold rr_frame in FR.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  step. if_true.
  step. step. step. step. step. step. step. step. step. step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. split; [reflexivity| exact ST].
Qed.

Lemma rrgen_tocpy : forall (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (A' A n E2 : Z),
  0 < A' < 2^64 -> 0 <= A <= E2 -> E2 < 2^64 -> 0 <= n < 2^64 ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x19d18) sp gp tp t0 t1 t2 (Z_to_bv 64 A') (Z_to_bv 64 A) (Z_to_bv 64 A') (Z_to_bv 64 A)
                                           (Z_to_bv 64 (Z.min n (E2 - A))) a3 a4 a5 a6 a7 (Z_to_bv 64 E2) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 0x240e0) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 A) (Z_to_bv 64 A') a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 E2) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19cf8) fc None m (seg_rom rsegs)).
Proof.
  intros until E2. intros HA' HA HE HN.
  step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }

  step. rewrite ?unsigned_lit by lia. step.
  step. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
  -   step. step. step. rewrite Z.min_l by lia. apply evt_done. reflexivity.
  -   step. step. step. step. rewrite Z.min_r by lia. apply evt_done. reflexivity.
Qed.

Lemma rrgen_tofree : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x19d20) sp gp tp t0 t1 t2 s0 s1 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 rfree_entry) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19d18) fc None m (seg_rom rsegs)).
Proof. intros. step. step. apply evt_done. reflexivity. Qed.

Lemma rrgen_end : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (ra0 q0 q1 q2 q3 q4 q5 q6 : word) F fc (m : mem) (lo : Z),
  rw_cells rsegs m (bv_unsigned sp + -64) (rr_frame q6 q5 q4 q3 q2 q1 q0 ra0) ->
  stk rsegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - 64 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 q0 q1 s0 a1 a2 a3 a4 a5 a6 a7 q2 q3 q4 q5 q6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra0) fc None m (seg_rom rsegs) /\ stk rsegs m lo (bv_unsigned sp))
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19d20) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros FR ST LO MI. unfold rr_frame in FR.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  step. step.
  step. step. step. step. step. step. step. step. step. step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. split; [reflexivity| exact ST].
Qed.
