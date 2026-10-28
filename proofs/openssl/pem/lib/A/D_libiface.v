(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition e_fuzz : Z := 0x1f3040.            (* [comment removed for export] *)
Definition RA_FUZZ : Z := 0x1f2f38.           (* [comment removed for export] *)
Definition FZ_EMPTY : Z := 0xb9f1a0.          (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition LIB_FP : list (Z * Z) :=
  (* [comment removed for export] *)
  [(0x5a9f20, 0x5a9f28); (0x5a9f40, 0x5a9f48); (0x5a9f60, 0x5a9f68); (0x5a9f80, 0x5a9f88); (0x5a9fc0, 0x5a9fc8);
   (0xb9f1c0, 0xb9f1e0); (0xb9f200, 0xb9f848); (0xb9f860, 0xb9f861); (0xba3e5a, 0xba3e5b); (0xba3e90, 0xba3e98); (0xbc4e58, 0xbc5270);
   (0xbc52a0, 0xbc5698); (0xb9f190, 0xb9f191)].

(* [comment removed for export] *)
Definition FUZZ_COST : Z := 2^31.
(* [comment removed for export] *)
Definition FUZZ_LIVE : Z := 16.
(* [comment removed for export] *)
Definition FUZZ_STACK : Z := 0x40000.

Section LibIface.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.

(* [comment removed for export] *)
Definition fuzz_one_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d : Z) (bs : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  ra = Z_to_bv 64 RA_FUZZ ->
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (Z.of_nat (length bs)) -> tp = Z_to_bv 64 0xba3ef0 ->
  0 < d -> Z.of_nat (length bs) < 2^26 -> bytes_at asegs m d bs ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d = FZ_EMPTY)) ->
  rt_frames RT Σ = [] -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  Z.of_nat (length (rt_live RT Σ)) + FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ ->
  (bv_unsigned s0 < bv_unsigned sp \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->
  LIB m -> io_ssp m -> ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= rt_sp0 RT Σ ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_fuzz m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) LIB_FP m m' /\ LIB m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = [] /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - FUZZ_COST <= rt_credit RT Σ').

End LibIface.
