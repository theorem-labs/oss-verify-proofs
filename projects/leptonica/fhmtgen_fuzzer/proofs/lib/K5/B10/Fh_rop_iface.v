(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Image.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit D_iface D_defs Lept_iface Gm_iface LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FhRopIface.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition raster1 (live : list (Z * Z)) (data w h wpl : Z) : Prop :=
  chunk live data (4 * (wpl * h)) /\ 0 < w <= 20000 /\ 0 < h <= 20000 /\ wpl = (w + 31) / 32 /\ 4 * (wpl * h) <= 0x4000000.

Definition rasteropUniLow_clr1_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (datad w h wpl dx dy dw dh : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 datad -> a1 = Z_to_bv 64 w -> a2 = Z_to_bv 64 h -> a3 = Z_to_bv 64 1 -> a4 = Z_to_bv 64 wpl ->
  a5 = Z_to_bv 64 dx -> a6 = Z_to_bv 64 dy -> a7 = Z_to_bv 64 dw ->
  rw_cells asegs m (bv_unsigned sp) [C8 (Z_to_bv 64 dh); C8 (Z_to_bv 64 0)] ->
  raster1 (rt_live RT Σ) datad w h wpl -> rect_in dx dy dw dh w h ->
  lenv RT Σ m sp lo (LSTK 1) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_rasteropUniLow m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(datad, datad + 4 * (wpl * h))] m m') c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ <= rt_credit RT Σ').

Definition rasteropLow_src1_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (datad dpw dph dwpl dx dy dw dh datas spw sph swpl sx sy : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 datad -> a1 = Z_to_bv 64 dpw -> a2 = Z_to_bv 64 dph -> a3 = Z_to_bv 64 1 -> a4 = Z_to_bv 64 dwpl ->
  a5 = Z_to_bv 64 dx -> a6 = Z_to_bv 64 dy -> a7 = Z_to_bv 64 dw ->
  rw_cells asegs m (bv_unsigned sp) [C8 (Z_to_bv 64 dh); C8 (Z_to_bv 64 12); C8 (Z_to_bv 64 datas); C8 (Z_to_bv 64 spw);
                                     C8 (Z_to_bv 64 sph); C8 (Z_to_bv 64 swpl); C8 (Z_to_bv 64 sx); C8 (Z_to_bv 64 sy)] ->
  raster1 (rt_live RT Σ) datad dpw dph dwpl -> raster1 (rt_live RT Σ) datas spw sph swpl -> datad <> datas ->
  rect_in dx dy dw dh dpw dph -> rect_in sx sy dw dh spw sph -> dx mod 32 = 0 -> sx mod 32 = 0 ->
  lenv RT Σ m sp lo (LSTK 1) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_rasteropLow m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(datad, datad + 4 * (dwpl * dph))] m m') c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ <= rt_credit RT Σ').
End FhRopIface.
