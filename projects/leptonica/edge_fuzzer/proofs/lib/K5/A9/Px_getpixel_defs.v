(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Image FP.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit D_iface D_defs D_libiface Lept_iface Ed_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition getpixel_case (RT : rt_sig) (al : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix pval x y : Z) (v : pixv) (cv : cmapv) (old : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> s32 a1 x -> s32 a2 y -> a3 = Z_to_bv 64 pval ->
  pix_obj (rt_live RT Σ) m pix v cv -> p_d v = 1 -> p_data v <> 0 ->
  optrF RT Σ m pval 4 -> rw_cells asegs m pval [C4 old] ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 1 0 GETPIXEL_COST -> bv_unsigned sp mod 32 = al ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixGetPixel m)))
    (fun c => exists (Σ' : rts RT) (b : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (getpixel_ret v x y)) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pval, pval + 4)] m m'
          /\ rw_cells asegs m' pval [C4 (Z_to_bv 64 b)]
          /\ (in_pix v x y -> pixel_val m v x y b) /\ (~ in_pix v x y -> b = 0) /\ (b = 0 \/ b = 1)) c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - GETPIXEL_COST <= rt_credit RT Σ').
