(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Image.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit D_iface D_defs Lept_iface Gq_gaps Gq_iface Gq_thr_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Definition e_numaSort : Z := 0x931d4.
Definition NSORT_COST : Z := 0.      (* [comment removed for export] *)
Definition e_pixcmapSetBlackAndWhite : Z := 0x98d60.
Definition e_makeGrayQuantTableArb : Z := 0xa1eac.
(* [comment removed for export] *)
Definition QTAB_RAS : list Z := [0x97538; 0xa2118].
Definition QTAB_COST : Z := 4.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition QTAB_VALS : list Z := repeat 0 45 ++ repeat 1 30 ++ repeat 2 40 ++ repeat 3 70 ++ repeat 4 71.

Section GqThr2Iface.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition optrS (Σ : rts RT) (sp s0 : word) (p n : Z) : Prop :=
  bv_unsigned sp <= p /\ p + n + 16 <= bv_unsigned s0 /\ bv_unsigned s0 <= rt_sp0 RT Σ /\ p mod 8 = 0.

(* [comment removed for export] *)
Definition numaSort_gq_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (na arr : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 na -> a1 = Z_to_bv 64 na -> a2 = Z_to_bv 64 1 ->
  numa_obj (rt_live RT Σ) m na 50 arr (map ival_w EDGE_VALS) ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 0 0 NSORT_COST ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_numaSort m)))
    (ASTA RT Σ PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 na) m' ms
          /\ lpost RT Σ Σ m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ numa_obj (rt_live RT Σ) m' na 50 arr (map ival_w EDGE_VALS))).

(* [comment removed for export] *)
Definition pixcmapSetBlackAndWhite00_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (cmap : Z) (cv : cmapv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 cmap -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 0 -> cmap_obj (rt_live RT Σ) m cmap cv ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 1 0 1 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixcmapSetBlackAndWhite m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [] m m' /\ cmap_obj (rt_live RT Σ') m' cmap cv) c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 1 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition makeGrayQuantTableArb_gq_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (ras : list Z) (na arr ptab pcmap : Z) (x1 x2 : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 na -> a1 = Z_to_bv 64 8 -> a2 = Z_to_bv 64 ptab -> a3 = Z_to_bv 64 pcmap ->
  numa_obj (rt_live RT Σ) m na 50 arr (map ival_w EDGE_VALS) ->
  optrS Σ sp s0 ptab 8 -> optrF RT Σ m pcmap 8 -> rw_cells asegs m ptab [C8 x1] -> rw_cells asegs m pcmap [C8 x2] -> ptab <> pcmap ->
  uctx m sp s0 ras -> Forall (fun f => In (f :: bv_unsigned ra :: ras) CLIENT_TRACES) QTAB_RAS ->
  lenv RT Σ m sp lo (LSTK 6) -> lres RT Σ 1 3 QTAB_COST ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_makeGrayQuantTableArb m)))
    (fun c => exists (Σ' : rts RT) (tab cmap carr : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
          /\ lpost RT Σ Σ' m m' sp lo
          /\ keepsL RT (rt_live RT Σ) Σ sp [(ptab, ptab + 8); (pcmap, pcmap + 8)] m m'
          /\ rw_cells asegs m' ptab [C8 (Z_to_bv 64 tab)] /\ rw_cells asegs m' pcmap [C8 (Z_to_bv 64 cmap)]
          /\ u32arr asegs m' tab (map (Z_to_bv 64) QTAB_VALS)
          /\ cmap_obj (rt_live RT Σ') m' cmap (mkCmapv carr 8 256 5)
          /\ numa_obj (rt_live RT Σ') m' na 50 arr (map ival_w EDGE_VALS)) c
       /\ rt_live RT Σ' = (tab, 1024) :: (carr, 1024) :: (cmap, 24) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - QTAB_COST <= rt_credit RT Σ').

End GqThr2Iface.
