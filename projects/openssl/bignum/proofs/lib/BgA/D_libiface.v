(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.bignum.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout RT_iface.
From OSSVerify.Proofs.openssl.bignum.lib.BgHXA Require Export HxaIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition e_fuzz : Z := 0x1f2fe8.

Definition LIB_FP : list (Z * Z) :=
  [(0x5aa520, 0x5aad40); (0xb9f790, 0xb9f791); (0xb9f7c0, 0xba3be0); (0xba445a, 0xba445b); (0xba4490, 0xba4498); (0xbc5458, 0xbc5898); (0xbc58a0, 0xbc5c98)].
Definition LIB_FPE : list (Z * Z) := (0xba444c, 0xba4450) :: LIB_FP.

Definition lib_startA (m : mem) : Prop := lib_pristineA m /\ rw_cells bgasegs m 0xb9f790 [C1 (Z_to_bv 8 0)].

Definition OSSL_BASE_INITED : Z := 0xb9f7c0.
Definition OSSL_DO_GLOBAL_CLEANUP : Z := 0xb9f7e0.
Definition lib_exit_cells (m : mem) : Prop :=
  exists b0 : byte, rw_cells bgasegs m OSSL_BASE_INITED [C1 b0] /\ rw_cells bgasegs m OSSL_DO_GLOBAL_CLEANUP [C1 (Z_to_bv 8 0)].

Definition FUZZ_COST : Z := 2^31.

Definition FUZZ_LIVE : Z := 80.

Definition FUZZ_STACK : Z := 0x20000.

Section LibIface.
Variable RT : rt_sig.

Variable LIBA : rts RT -> list (Z * Z) -> mem -> Prop.

Definition fuzz_one_cps' : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d : Z) (bs : list byte) (lo : Z) (LW CL : list (Z * Z)),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (Z.of_nat (length bs)) -> tp = Z_to_bv 64 0xba44f0 ->
  0 < d < 2^64 -> d <= lo ->
  Z.of_nat (length bs) < 2^26 -> bytes_at bgasegs m d bs ->
  ((exists p n, In (p, n) CL /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ bs = []) ->
  Permutation (rt_live RT Σ) (LW ++ CL) -> LIBA Σ LW m ->
  rt_frames RT Σ = [] -> (forall p n, In (p, n) CL -> 0 < n) ->
  Z.of_nat (length (rt_live RT Σ)) + FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ ->
  (bv_unsigned s0 <= lo \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->
  ART RT Σ m -> mem_inv bgasegs m ->
  stk bgasegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= rt_sp0 RT Σ ->
  cps bgasegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_fuzz m)))
    (fun c => exists (Σ' : rts RT) (LW' : list (Z * Z)),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp CL [] (bv_unsigned sp) LIB_FPE m m' /\ LIBA Σ' LW' m') c
       /\ Permutation (rt_live RT Σ') (LW' ++ CL) /\ rt_frames RT Σ' = [] /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - FUZZ_COST <= rt_credit RT Σ'
       /\ Z.of_nat (length (rt_live RT Σ')) <= Z.of_nat (length (rt_live RT Σ)) + FUZZ_LIVE).

Definition liba_frame : Prop :=
  forall (Σ Σ' : rts RT) (LW : list (Z * Z)) (m m' : mem), LIBA Σ LW m ->
    (forall a : word, in_ranges LIB_FP (bv_unsigned a) \/ in_live LW (bv_unsigned a) -> m' a = m a) -> LIBA Σ' LW m'.

Definition liba_exit : Prop := forall (Σ : rts RT) (LW : list (Z * Z)) (m : mem), LIBA Σ LW m -> lib_exit_cells m.

Definition liba_pos : Prop := forall (Σ : rts RT) (LW : list (Z * Z)) (m : mem), LIBA Σ LW m -> forall p n, In (p, n) LW -> 0 < n.

End LibIface.
