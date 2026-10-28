(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac ZBridge RzCPS Cells Mem Frame. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition e_strcpy : Z := 0x1ad70c.

(* [comment removed for export] *)
Definition strcpy_icontract (RT : rt_sig) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d s : Z) (str slack : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s ->
  bytes_at ctasegs m s (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2^40 ->
  (- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  0 < s <= 2^47 -> 0 < d <= 2^47 ->
  (s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= s) ->
  checked_src RT Σ m sp lo s (Z.of_nat (length str) + 1) -> checked_dst RT Σ m sp d (Z.of_nat (length str) + 1) ->
  (d + Z.of_nat (length str) + 1 <= s \/ s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= d) ->
  ART RT Σ m -> mem_inv ctasegs m -> call_ok RT Σ m sp lo ->
  cps ctasegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_strcpy m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 d) lo d (Z.of_nat (length str) + 1) m
               (fun m' => bytes_at ctasegs m' d (str ++ [Z_to_bv 8 0]))).
