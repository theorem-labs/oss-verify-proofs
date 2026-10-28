(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_libiface Sj_akit Sj_acps Atp_activewA Pj_defsA Imp_hdefs0A Imp_libifaceA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition GRSI_STACK_A : Z := 4096 + RT_STACK.

Definition GRSI_COST_A : Z := mcost 8 + 16.

Definition GRSI_LIVE_A : Z := 2.

Definition GRSI_FRAMES_A : nat := 2.

Definition GRSI_W : list (Z * Z) :=
  [(IMP_VEC_OBJ_A, IMP_VEC_OBJ_A + 24); (IMP_AVL_GUARD_A, IMP_AVL_GUARD_A + 2); (IMP_AVP_SPAN_A, IMP_AVP_SPAN_A + 16); (IMP_AVP_GUARD_A, IMP_AVP_GUARD_A + 2);
   (IMP_AVP_ARR_A, IMP_AVP_ARR_A + 8); (SJ_SINGLETON, SJ_SINGLETON + 44); (0x6bc220, 0x6bc222)].

Definition grsi_preA (m : mem) : Prop :=
  lib0 m /\ rw_cells bsegs m IMP_AVL_GUARD_A g00
  /\ rw_cells bsegs m IMP_AVP_SPAN_A [C8 (wz 0); C8 (wz 0)] /\ rw_cells bsegs m IMP_AVP_GUARD_A g00 /\ rw_cells bsegs m IMP_AVP_ARR_A [C8 (wz 0)]
  /\ rw_cells bsegs m IMP_VEC_OBJ_A [C8 (wz 0); C8 (wz 0); C8 (wz 0)].

Definition grsi_postA (A8 : Z) (m : mem) : Prop :=
  libm m /\ rw_cells bsegs m IMP_AVL_GUARD_A g11
  /\ rw_cells bsegs m IMP_AVP_SPAN_A [C8 (wz IMP_AVP_ARR_A); C8 (wz 1)] /\ rw_cells bsegs m IMP_AVP_GUARD_A g11 /\ rw_cells bsegs m IMP_AVP_ARR_A [C8 (wz SJ_SINGLETON)]
  /\ rw_cells bsegs m IMP_VEC_OBJ_A [C8 (wz A8); C8 (wz (A8 + 8)); C8 (wz (A8 + 8))]
  /\ rw_cells bsegs m A8 [C8 (wz SJ_SINGLETON)].

Section GrsiStmt.
Variable RT : rt_sig.

Definition grsi_icontractA : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = wz IMP_VEC_OBJ_A -> tp = wz TPV_A ->
  grsi_preA m ->
  (length (rt_frames RT Σ) + GRSI_FRAMES_A <= FRAMES_MAX)%nat -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  Z.of_nat (length (rt_live RT Σ)) + GRSI_LIVE_A <= LIVE_MAX -> GRSI_COST_A <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + GRSI_STACK_A <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> unwind_ok ra s0 sp -> frm0 fc ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc IMP_GRSI_A m)))
    (fun c => exists (Σ' : rts RT) (A8 : Z),
       ASTA RT Σ' PMc (fun ms => exists (v : word) m', ret_stF fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) GRSI_W m m'
         /\ grsi_postA A8 m') c
       /\ rt_live RT Σ' = (A8, 8) :: rt_live RT Σ /\ 0 < A8 /\ A8 mod 16 = 0
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - GRSI_COST_A <= rt_credit RT Σ').

End GrsiStmt.
