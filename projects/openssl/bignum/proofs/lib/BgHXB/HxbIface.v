(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.bignum.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout RT_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition e_init : Z := 0x1edfd0.

Definition INIT_STACK : Z := 0x40010.

Definition INIT_COST : Z := 2048.

Definition INIT_LIVE : Z := 1600.

Definition LIB_PRISTINE : list (Z * Z) :=
  [(0x5e2880, 0x5e3360); (0xbd20c0, 0xbd29a0); (0xbd6d90, 0xbd6d98); (0xbf7d60, 0xbf8198); (0xbf81a0, 0xbf81e0)].
Definition lib_pristineA (m : mem) : Prop :=
  (forall a, in_ranges LIB_PRISTINE a -> mrd bgbsegs m (wa a) = seg_rom bgbsegs (wa a))
  /\ rw_cells bgbsegs m 0xbf7d58 [C8 (Z_to_bv 64 0x1c06d8)].

Definition LIBW_HXA : list (Z * Z) :=
  [(0x5e2880, 0x5e3360); (0xbd20c0, 0xbd29a0); (0xbd6d4c, 0xbd6d50); (0xbd6d5a, 0xbd6d5b); (0xbd6d90, 0xbd6d98); (0xbf7d58, 0xbf8198); (0xbf81a0, 0xbf81e0)].

Section InitIface.
Variable RT : rt_sig.

Variable LIBA : rts RT -> list (Z * Z) -> mem -> Prop.

Definition init_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xbd6df0 ->
  rt_frames RT Σ = [] -> Z.of_nat (length (rt_live RT Σ)) + INIT_LIVE <= LIVE_MAX -> INIT_COST <= rt_credit RT Σ ->

  (bv_unsigned s0 <= lo \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->
  lib_pristineA m -> ART RT Σ m -> mem_inv bgbsegs m ->
  stk bgbsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + INIT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  cps bgbsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_init m)))
    (fun c => exists (Σ' : rts RT) (LW : list (Z * Z)) (v : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) [] (bv_unsigned sp) LIBW_HXA m m' /\ LIBA Σ' LW m') c
       /\ rt_live RT Σ' = LW ++ rt_live RT Σ /\ Z.of_nat (length LW) <= INIT_LIVE /\ rt_frames RT Σ' = [] /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - INIT_COST <= rt_credit RT Σ').

End InitIface.
