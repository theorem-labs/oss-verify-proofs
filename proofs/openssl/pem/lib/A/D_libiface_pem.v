(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition e_fuzz_init : Z := 0x1f303c.       (* [comment removed for export] *)
Definition RA_INIT : Z := 0x1f2fc0.           (* [comment removed for export] *)
Definition e_fuzz : Z := 0x1f3040.            (* [comment removed for export] *)
Definition RA_FUZZ : Z := 0x1f2f38.           (* [comment removed for export] *)
Definition FZ_EMPTY : Z := 0xb9f1a0.          (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition LIB_W : list (Z * Z) :=
  [(0x5a9f20, 0x5a9f24); (0xb9f1c0, 0xb9f1e0); (0xb9f200, 0xb9f848); (0xba3e4c, 0xba3e50); (0xba3e5a, 0xba3e5b); (0xba3e90, 0xba3e98);
   (0xbc4e60, 0xbc5268); (0xbc52a0, 0xbc5698)].   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition INIT_COST : Z := 2^20.
Definition FUZZ_COST : Z := 2^33.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition CLI_MAX : Z := 6000.
Definition FUZZ_LIVE : Z := 64.
(* [comment removed for export] *)
Definition FUZZ_STACK : Z := 0x40000.

Section LibIface.
Variable RT : rt_sig.
Variable LIB0 : mem -> Prop.
Variable LIB : list (Z * Z) -> mem -> Prop.
(* [comment removed for export] *)
Variables FZ_SITES FZ_CALLS : list (Z * Z).

(* [comment removed for export] *)
Definition cli_pres (DRV : list (Z * Z)) (sp : Z) (m m' : mem) : Prop := rt_pres_fp DRV [] sp LIB_W m m'.

(* [comment removed for export] *)
Definition fuzz_init_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  ra = Z_to_bv 64 RA_INIT -> tp = Z_to_bv 64 0xba3ef0 ->
  rt_frames RT Σ = [] -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  Z.of_nat (length (rt_live RT Σ)) + CLI_MAX + FUZZ_LIVE <= LIVE_MAX -> INIT_COST <= rt_credit RT Σ ->
  (* [comment removed for export] *)
  fp_invalid s0 (Z_to_bv 64 (bv_unsigned sp - 16)) -> cg_has (rt_cg RT Σ) FZ_SITES FZ_CALLS ->
  LIB0 m -> io_ssp m -> (exists v, rw_cells asegs m (errno_cell tp) [C4 v]) -> ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= rt_sp0 RT Σ ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_fuzz_init m)))
    (fun c => exists (Σ' : rts RT) (CL : list (Z * Z)),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ cli_pres (rt_live RT Σ) (bv_unsigned sp) m m' /\ LIB CL m' /\ (exists v, rw_cells asegs m' (errno_cell tp) [C4 v])) c
       /\ Permutation (rt_live RT Σ') (CL ++ rt_live RT Σ) /\ Z.of_nat (length CL) <= CLI_MAX /\ (forall p n, In (p, n) CL -> 0 < n)
       /\ rt_frames RT Σ' = [] /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - INIT_COST <= rt_credit RT Σ'
       /\ rt_cg RT Σ' = rt_cg RT Σ).

(* [comment removed for export] *)
Definition fuzz_one_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d : Z) (bs : list byte) (CL DRV : list (Z * Z)) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  ra = Z_to_bv 64 RA_FUZZ ->
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (Z.of_nat (length bs)) -> tp = Z_to_bv 64 0xba3ef0 ->
  0 < d -> Z.of_nat (length bs) < 2^26 -> bytes_at asegs m d bs ->
  ((exists p n, In (p, n) DRV /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d = FZ_EMPTY)) ->
  Permutation (rt_live RT Σ) (CL ++ DRV) -> Z.of_nat (length CL) <= CLI_MAX ->
  rt_frames RT Σ = [] -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  Z.of_nat (length DRV) + CLI_MAX + FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ ->
  fp_invalid s0 sp -> cg_has (rt_cg RT Σ) FZ_SITES FZ_CALLS ->
  LIB CL m -> io_ssp m -> (exists v, rw_cells asegs m (errno_cell tp) [C4 v]) -> ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= rt_sp0 RT Σ ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_fuzz m)))
    (fun c => exists (Σ' : rts RT) (CL' : list (Z * Z)),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ cli_pres DRV (bv_unsigned sp) m m' /\ LIB CL' m' /\ (exists v, rw_cells asegs m' (errno_cell tp) [C4 v])) c
       /\ Permutation (rt_live RT Σ') (CL' ++ DRV) /\ Z.of_nat (length CL') <= CLI_MAX /\ (forall p n, In (p, n) CL' -> 0 < n)
       /\ rt_frames RT Σ' = [] /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - FUZZ_COST <= rt_credit RT Σ'
       /\ rt_cg RT Σ' = rt_cg RT Σ).

(* [comment removed for export] *)
Definition lib0_local : Prop :=
  forall m m', LIB0 m -> (forall a : word, in_ranges LIB_W (bv_unsigned a) -> m' a = m a) -> LIB0 m'.
Definition lib_local : Prop :=
  forall CL m m', LIB CL m -> (forall a : word, in_ranges LIB_W (bv_unsigned a) \/ in_live CL (bv_unsigned a) -> m' a = m a) -> LIB CL m'.

(* [comment removed for export] *)
Definition LIB_D : list (Z * Z) :=
  (* [comment removed for export] *)
  [(0x5a9f20, 0x5a9f28); (0x5a9f40, 0x5a9f48); (0x5a9f60, 0x5a9f68); (0x5a9f80, 0x5a9f88); (0x5a9fc0, 0x5a9fc8);
   (0xb9f1c0, 0xb9f1e0); (0xb9f200, 0xb9f848); (0xb9f860, 0xb9f861); (0xba3e5a, 0xba3e5b); (0xba3e90, 0xba3e98); (0xbc4e58, 0xbc5270);
   (0xbc52a0, 0xbc5698)].
Definition lib0_local_d : Prop :=
  forall m m', LIB0 m -> (forall a : word, in_ranges LIB_D (bv_unsigned a) -> m' a = m a) -> LIB0 m'.
Definition lib_local_d : Prop :=
  forall CL m m', LIB CL m -> (forall a : word, in_ranges LIB_D (bv_unsigned a) \/ in_live CL (bv_unsigned a) -> m' a = m a) -> LIB CL m'.

End LibIface.
