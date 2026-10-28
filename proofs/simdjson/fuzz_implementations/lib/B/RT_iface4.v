(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Mem Frame Cells ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Contracts4.
Variable RT : rt_sig.

Definition stack_malloc1z_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0x6be3e8 ->
  (length (rt_frames RT Σ) < FRAMES_MAX2)%nat -> 1 <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  rt_frames RT Σ <> [] ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_stack_malloc_1 m)))
    (fun c => exists (Σ' : rts RT) (f : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 f) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ wr_at bsegs m' f (fs_size 1 - 8) /\ wr_at bsegs m' (shad f) (fs_size 1 / 8)
         /\ rw_cells bsegs m' (shad f) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) c
       /\ rt_frames RT Σ' = (f, 1%nat) :: rt_frames RT Σ /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ 0 < f /\ f mod 64 = 0 /\ f + fs_size 1 < USTACK_TOP).
End Contracts4.
