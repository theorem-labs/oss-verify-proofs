(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition e_init : Z := 0x1f40ec.
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
  [(0x5aebe0, 0x5af400); (0xba46c0, 0xba4fa0); (0xba9390, 0xba9398); (0xbca360, 0xbca798); (0xbca7a0, 0xbca7e0)].
Definition lib_pristineA (m : mem) : Prop :=
  (forall a, in_ranges LIB_PRISTINE a -> mrd ctasegs m (wa a) = seg_rom ctasegs (wa a))
  /\ rw_cells ctasegs m 0xbca358 [C8 (Z_to_bv 64 0x1c67f4)].

(* [comment removed for export] *)
Definition LIBW_HXA : list (Z * Z) :=
  [(0x5aebe0, 0x5af400); (0xba46c0, 0xba4fa0); (0xba934c, 0xba9350); (0xba935a, 0xba935b); (0xba9390, 0xba9398); (0xbca358, 0xbca798); (0xbca7a0, 0xbca7e0)].

Section InitIface.
Variable RT : rt_sig.
(* [comment removed for export] *)
Variable LIBA : rts RT -> list (Z * Z) -> mem -> Prop.

Definition init_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba93f0 ->
  rt_frames RT Σ = [] -> lroom3 (rt_live RT Σ) INIT_LIVE INIT_PB INIT_NB -> INIT_COST <= rt_credit RT Σ ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (bv_unsigned s0 <= lo \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->
  lib_pristineA m -> ART RT Σ m -> mem_inv ctasegs m ->
  stk ctasegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + INIT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  cps ctasegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_init m)))
    (fun c => exists (Σ' : rts RT) (LW : list (Z * Z)) (v : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) [] (bv_unsigned sp) LIBW_HXA m m' /\ LIBA Σ' LW m') c
       /\ rt_live RT Σ' = LW ++ rt_live RT Σ /\ (Z.of_nat (length LW) <= INIT_LIVE /\ psum LW <= INIT_PB /\ nbig LW <= INIT_NB) /\ rt_frames RT Σ' = [] /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - INIT_COST <= rt_credit RT Σ').

End InitIface.
