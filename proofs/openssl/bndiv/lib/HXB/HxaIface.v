(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition e_init : Z := 0x1ee358.
(* [comment removed for export] *)
Definition INIT_STACK : Z := 0x40010.
(* [comment removed for export] *)
Definition INIT_COST : Z := 2048.
(* [comment removed for export] *)
Definition INIT_LIVE : Z := 1600.

(* [comment removed for export] *)
Definition LIB_PRISTINE : list (Z * Z) :=
  [(0x5e6660, 0x5e7140); (0xbd6080, 0xbd6a60); (0xbdadf0, 0xbdadf8); (0xbfbdc0, 0xbfc1f8); (0xbfc200, 0xbfc240)].
Definition lib_pristineA (m : mem) : Prop :=
  (forall a, in_ranges LIB_PRISTINE a -> mrd bsegs m (wa a) = seg_rom bsegs (wa a))
  /\ rw_cells bsegs m 0xbfbdb8 [C8 (Z_to_bv 64 0x1c0a60)].

(* [comment removed for export] *)
Definition LIBW_HXA : list (Z * Z) :=
  [(0x5e6660, 0x5e7140); (0xbd6080, 0xbd6a60); (0xbdadac, 0xbdadb0); (0xbdadba, 0xbdadbb); (0xbdadf0, 0xbdadf8); (0xbfbdb8, 0xbfc1f8); (0xbfc200, 0xbfc240)].

Section InitIface.
Variable RT : rt_sig.
(* [comment removed for export] *)
Variable LIBA : rts RT -> list (Z * Z) -> mem -> Prop.

Definition init_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xbdae50 ->
  rt_frames RT Σ = [] -> Z.of_nat (length (rt_live RT Σ)) + INIT_LIVE <= LIVE_MAX -> INIT_COST <= rt_credit RT Σ ->
  (* [comment removed for export] *)
  (bv_unsigned s0 <= lo \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->
  lib_pristineA m -> ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + INIT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_init m)))
    (fun c => exists (Σ' : rts RT) (LW : list (Z * Z)) (v : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) [] (bv_unsigned sp) LIBW_HXA m m' /\ LIBA Σ' LW m') c
       /\ rt_live RT Σ' = LW ++ rt_live RT Σ /\ Z.of_nat (length LW) <= INIT_LIVE /\ rt_frames RT Σ' = [] /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - INIT_COST <= rt_credit RT Σ').

End InitIface.
