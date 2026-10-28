(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjNumber.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition NUMA_STACK : Z := 1024 + RT_STACK.
Definition NUMA_FRAMES : nat := 3.
Definition NUMA_CREDIT : Z := 16.

Section NumIface.
Variable RT : rt_sig.

Definition numwa_cps (entry r1 r0 : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (A off stop OUT lo p n : Z) (txt : list byte) (b : byte) (junk : list byte),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 (A + off) -> a1 = Z_to_bv 64 OUT -> tp = Z_to_bv 64 0x6ab368 ->
  frm0 fc ->

  (length (rt_frames RT Σ) + NUMA_FRAMES <= FRAMES_MAX)%nat -> rt_frames RT Σ <> [] -> NUMA_CREDIT <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + NUMA_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->

  In (p, n) (rt_live RT Σ) -> p mod 8 = 0 -> p <= A -> A + stop + 8 <= p + n -> A + Z.of_nat (length txt) <= p + n ->
  bytes_at bsegs m A txt -> Z.of_nat (length txt) < 2147483648 ->
  0 <= off <= stop -> nth_error txt (Z.to_nat stop) = Some b -> numchar (bv_unsigned b) = false ->

  rw_cells bsegs m OUT [CB 8 junk] -> bv_unsigned sp <= OUT -> OUT + 8 <= USTACK_TOP -> OUT mod 8 = 0 ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc entry m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m' v (flag : bool),
           ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (if flag then r1 else r0)) m' ms
         /\ frm0 (ms_fcsr ms)
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) OUT 8 m m'
         /\ rw_cells bsegs m' OUT [C8 v]) c
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - NUMA_CREDIT <= rt_credit RT Σ').

Definition slowfa_cps : Prop := numwa_cps 0xee144 9 0.
Definition pffa_cps : Prop := numwa_cps 0xee248 0 1.

End NumIface.
