(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Contracts.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition realloc_contract_gen : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (p n0 n lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  In (p, n0) (rt_live RT Σ) -> 1 <= n <= 0x8000000 ->
  a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 n -> tp = Z_to_bv 64 0xba93f0 ->
  live_room (rt_live RT Σ) n -> mcost n <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv ctasegs m -> call_ok RT Σ m sp lo -> unwind_ch m ra s0 sp ->
  cps ctasegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_realloc m)))
            (realloc_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p n0 n lo m).

(* [comment removed for export] *)
Lemma realloc_contract_gen_prim : realloc_contract_gen -> realloc_contract RT.
Proof.
  intros H Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n0 n lo
         F1 F2 HIN Hn0 Hn HA0 HA1 HTP LR CR HART MI CO UC.
  apply (H Σ PMc); try assumption. lia.
Qed.
End Contracts.
