(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Tac ITree Nodes SysStep.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Pm6 Require Import F_syscalls_u5.
Import ListNotations.
Open Scope bv_scope.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Abbreviation RVMLOCK := 0xfdc04%Z.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.

Definition rvmwait_entry : Z := 0xc0714%Z.

Definition rvmwait_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' RVMLOCK [C4 (Z_to_bv 64 0)].

Lemma rvmwait_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (lo : Z),
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m RVMLOCK [C4 (Z_to_bv 64 0)] ->
  mem_inv rsegs m ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (0xfe000 <= lo)%Z ->
  evt rsegs (rvmwait_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xc0714) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST VL MI LO SLO.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  do 4 step. (* [comment removed for export] *)
  do 2 step. (* [comment removed for export] *)
  step.      (* [comment removed for export] *)
  step.      (* [comment removed for export] *)
  if_cases K; zify_cond K.
  2:{ exfalso. apply K. reflexivity. }
  do 5 step.
  release_frame FR ST (bv_unsigned sp).
  unfold rvmwait_post. finish.
Qed.

End CEIL_WRAP_1.
