(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec RzCPS. 
From OSSVerify.Proofs.openssl.ct.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.ct.lib.CtB Require Import Layout RT_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition e_init : Z := 0x1ef07c.
(* [comment removed for export] *)
Definition INIT_STACK : Z := 0x40010.
(* [comment removed for export] *)
Definition INIT_COST : Z := 4096.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition INIT_LIVE : Z := 1700.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition INIT_PB : Z := INIT_LIVE * LW_MAX.   (* [comment removed for export] *)
Definition INIT_NB : Z := INIT_LIVE.            (* [comment removed for export] *)

(* [comment removed for export] *)
Definition LIB_PRISTINE : list (Z * Z) :=
  [(0x5e74e0, 0x5e7fc0); (0xbd7500, 0xbd7de0); (0xbdc1d0, 0xbdc1d8); (0xbfd1a0, 0xbfd5d8); (0xbfd5e0, 0xbfd620)].
Definition lib_pristineA (m : mem) : Prop :=
  (forall a, in_ranges LIB_PRISTINE a -> mrd ctbsegs m (wa a) = seg_rom ctbsegs (wa a))
  /\ rw_cells ctbsegs m 0xbfd198 [C8 (Z_to_bv 64 0x1c1784)].

(* [comment removed for export] *)
Definition LIBW_HXA : list (Z * Z) :=
  [(0x5e74e0, 0x5e7fc0); (0xbd7500, 0xbd7de0); (0xbdc18c, 0xbdc190); (0xbdc19a, 0xbdc19b); (0xbdc1d0, 0xbdc1d8); (0xbfd198, 0xbfd5d8); (0xbfd5e0, 0xbfd620)].

Section InitIface.
Variable RT : rt_sig.
(* [comment removed for export] *)
Variable LIBA : rts RT -> list (Z * Z) -> mem -> Prop.

Definition init_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xbdc230 ->
  rt_frames RT Σ = [] -> lroom3 (rt_live RT Σ) INIT_LIVE INIT_PB INIT_NB -> INIT_COST <= rt_credit RT Σ ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (bv_unsigned s0 <= lo \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->
  lib_pristineA m -> ART RT Σ m -> mem_inv ctbsegs m ->
  stk ctbsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + INIT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  cps ctbsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_init m)))
    (fun c => exists (Σ' : rts RT) (LW : list (Z * Z)) (v : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) [] (bv_unsigned sp) LIBW_HXA m m' /\ LIBA Σ' LW m') c
       /\ rt_live RT Σ' = LW ++ rt_live RT Σ /\ (Z.of_nat (length LW) <= INIT_LIVE /\ psum LW <= INIT_PB /\ nbig LW <= INIT_NB) /\ rt_frames RT Σ' = [] /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - INIT_COST <= rt_credit RT Σ').

End InitIface.
