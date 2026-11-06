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
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit D_iface D_defs D_libiface Lept_iface Ed_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition profile_case (RT : rt_sig) (al : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (cv : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 0 ->
  pix_obj (rt_live RT Σ) m pix v cv -> p_d v = 1 -> p_data v <> 0 ->
  uctx m sp s0 ras -> numaCreate_trace_ok (bv_unsigned ra :: ras) ->
  lenv RT Σ m sp lo (LSTK 6) -> lres RT Σ 4 2 (PROFILE_COST (p_w v) (p_h v)) -> bv_unsigned sp mod 32 = al ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixGetEdgeProfile m)))
    (fun c => exists (Σ' : rts RT) (na arr : Z) (ks : list Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 na) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ numa_obj (rt_live RT Σ') m' na (p_h v) arr (map ival_w ks)) c
       /\ Z.of_nat (length ks) = p_h v /\ Forall (fun k => loc_ok k /\ k <= p_w v - 1) ks
       /\ rt_live RT Σ' = numa_live na (p_h v) arr (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - PROFILE_COST (p_w v) (p_h v) <= rt_credit RT Σ').
