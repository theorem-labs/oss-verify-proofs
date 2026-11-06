(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit D_iface D_defs Lept_iface Gm_iface Gq_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition bytew (w : word) : Prop := bv_unsigned w <= 255.
Definition byte_arr (m : mem) (p n : Z) : Prop :=
  exists ws : list word, u32arr asegs m p ws /\ Z.of_nat (length ws) = n /\ Forall bytew ws.

Section GqCmapIface.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition pixcmapToArrays_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (cmap : Z) (cv : cmapv) (pr pg pb pa : Z) (x1 x2 x3 x4 : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 cmap -> a1 = Z_to_bv 64 pr -> a2 = Z_to_bv 64 pg -> a3 = Z_to_bv 64 pb -> a4 = Z_to_bv 64 pa ->
  cmap_obj (rt_live RT Σ) m cmap cv -> 1 <= c_n cv ->
  optrF RT Σ m pr 8 -> optrF RT Σ m pg 8 -> optrF RT Σ m pb 8 -> optrF RT Σ m pa 8 ->
  rw_cells asegs m pr [C8 x1] -> rw_cells asegs m pg [C8 x2] -> rw_cells asegs m pb [C8 x3] -> rw_cells asegs m pa [C8 x4] ->
  pr <> pg /\ pr <> pb /\ pr <> pa /\ pg <> pb /\ pg <> pa /\ pb <> pa ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 0 4 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixcmapToArrays m)))
    (fun c => exists (Σ' : rts RT) (rmap gmap bmap amap : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
          /\ lpost RT Σ Σ' m m' sp lo
          /\ keepsL RT (rt_live RT Σ) Σ sp [(pr, pr + 8); (pg, pg + 8); (pb, pb + 8); (pa, pa + 8)] m m'
          /\ rw_cells asegs m' pr [C8 (Z_to_bv 64 rmap)] /\ rw_cells asegs m' pg [C8 (Z_to_bv 64 gmap)]
          /\ rw_cells asegs m' pb [C8 (Z_to_bv 64 bmap)] /\ rw_cells asegs m' pa [C8 (Z_to_bv 64 amap)]
          /\ byte_arr m' rmap (c_n cv) /\ byte_arr m' gmap (c_n cv) /\ byte_arr m' bmap (c_n cv) /\ byte_arr m' amap (c_n cv)) c
       /\ rt_live RT Σ' = (amap, 4 * c_n cv) :: (bmap, 4 * c_n cv) :: (gmap, 4 * c_n cv) :: (rmap, 4 * c_n cv) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ <= rt_credit RT Σ').

End GqCmapIface.
