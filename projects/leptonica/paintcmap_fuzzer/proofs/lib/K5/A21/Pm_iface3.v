(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import ImageA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import Layout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Pm_iface D_iface D_defs.
Import ListNotations.
Open Scope Z_scope.

Definition PM_BOXCREATE_CALLOC : Z := 0x8df08.     (* [comment removed for export] *)

Section PmIface3.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition boxCreate_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (x y w h : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 x -> a1 = Z_to_bv 64 y -> a2 = Z_to_bv 64 w -> a3 = Z_to_bv 64 h ->
  0 <= x < 2^31 -> 0 <= y < 2^31 -> 0 <= w < 2^31 -> 0 <= h < 2^31 ->
  lenv RT Σ m sp lo (LSTK 1) -> lres RT Σ 0 1 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_boxCreate m)))
    (fun c => exists (Σ' : rts RT) (b : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 b) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m' /\ box_obj (rt_live RT Σ') m' b x y w h) c
       /\ rt_live RT Σ' = (b, 20) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ).
End PmIface3.
