(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Image FP.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit D_iface D_defs D_libiface Lept_iface.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Export Gq_numa Gq_obj Gm_iface Gq_gaps.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_stringNew : Z := 0x91068.
Definition e_strtokSafe : Z := 0x91384.
Definition e_pixCopyInputFormat : Z := 0x95204.
Definition e_pixSetSpp : Z := 0x959f4.
Definition e_pixClone : Z := 0x95b0c.
Definition e_extractRGBValues : Z := 0x96ea8.
Definition e_pixcmapCreate : Z := 0x974f0.
Definition e_pixcmapAddColor : Z := 0x9767c.
Definition e_pixcmapCreateLinear : Z := 0x978d0.
Definition e_pixcmapGetCount : Z := 0x986d8.
Definition e_pixcmapSetBlackAndWhite : Z := 0x98d60.
Definition e_pixcmapToArrays : Z := 0x998e4.
Definition e_pixRemoveColormap : Z := 0x9aebc.
Definition e_pixDitherToBinary : Z := 0x9d968.       (* [comment removed for export] *)
Definition e_pixDitherToBinarySpec : Z := 0x9da84.
Definition e_ditherToBinaryLow : Z := 0x9e0ac.
Definition e_ditherToBinaryLineLow : Z := 0x9e2d8.
Definition e_pixGenerateMaskByBand : Z := 0x9eb78.
Definition e_pixDitherTo2bpp : Z := 0x9f3dc.         (* [comment removed for export] *)
Definition e_pixDitherTo2bppSpec : Z := 0x9f510.
Definition e_pixThresholdGrayArb : Z := 0xa0ce4.
Definition e_makeGrayQuantTableArb : Z := 0xa1eac.
Definition e_pixGenerateMaskByBand32 : Z := 0xa2460.
Definition e_pixGenerateMaskByDiscr32 : Z := 0xa2d20.
Definition e_parseStringForNumbers : Z := 0xb08ac.

(* [comment removed for export] *)
Definition RA_FUZZ_OP1 : Z := 0x90ad8.   (* [comment removed for export] *)
Definition RA_FUZZ_OP2 : Z := 0x90b04.   (* [comment removed for export] *)
Definition RA_FUZZ_OP3 : Z := 0x90b3c.   (* [comment removed for export] *)
Definition RA_FUZZ_OP4 : Z := 0x90b78.   (* [comment removed for export] *)
Definition RA_FUZZ_OP5 : Z := 0x90bac.   (* [comment removed for export] *)
Definition RA_FUZZ_OP6 : Z := 0x90bec.   (* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MSG_COST : Z := 4.                           (* [comment removed for export] *)
(* [comment removed for export] *)
Definition REMOVE_COST : Z := RASTER_COST + 16.         (* [comment removed for export] *)
Definition is_d8 (d : Z) : bool := d =? 8.
Definition is_d32 (d : Z) : bool := d =? 32.
Definition is_d248 (d : Z) : bool := (d =? 2) || (d =? 4) || (d =? 8).
Definition OP_COST (live_d : Z -> bool) (rasters : Z) (d : Z) : Z := if live_d d then rasters * RASTER_COST + 64 else MSG_COST.
Definition D2_COST : Z -> Z := OP_COST is_d8 2.         (* [comment removed for export] *)
Definition DBIN_COST : Z -> Z := OP_COST is_d8 2.       (* [comment removed for export] *)
Definition BAND_COST : Z -> Z := OP_COST is_d248 1.     (* [comment removed for export] *)
Definition BAND32_COST : Z -> Z := OP_COST is_d32 1.
Definition DISCR32_COST : Z -> Z := OP_COST is_d32 1.
Definition THR_COST : Z -> Z := OP_COST is_d8 2.        (* [comment removed for export] *)
(* [comment removed for export] *)
Definition GQ_FUZZ_NEED (d : Z) : Z :=
  1 + (RASTER_COST + 64) + 6 * TEMPLATE_COST
  + (D2_COST d + DBIN_COST d + BAND_COST d + BAND32_COST d + DISCR32_COST d + THR_COST d) + 13 + 16.
Lemma gq_fuzz_need_ok : forall d, GQ_FUZZ_NEED d <= FUZZ_COST.
Proof.
  intros d. unfold GQ_FUZZ_NEED, D2_COST, DBIN_COST, BAND_COST, BAND32_COST, DISCR32_COST, THR_COST, OP_COST, is_d8, is_d32, is_d248,
    TEMPLATE_COST, MSG_COST, RASTER_COST, FUZZ_COST.
  destruct (Z.eqb_spec d 8) as [-> | N8]; [ cbn; lia | ].
  destruct (Z.eqb_spec d 32) as [-> | N32]; [ cbn; lia | ].
  destruct (d =? 2); destruct (d =? 4); cbn; lia.
Qed.

(* [comment removed for export] *)

Section GqIface.
Variable RT : rt_sig.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pixCreate_sure_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (w h d : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  s32 a0 w -> s32 a1 h -> s32 a2 d -> hdr_args_ok w h d ->
  lenv RT Σ m sp lo (LSTK 5) -> lres RT Σ 3 2 (RASTER_COST + 8) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCreate m)))
    (fun c => exists (Σ' : rts RT) (pix : Z) (v : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pix) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix_obj (rt_live RT Σ') m' pix v (mkCmapv 0 0 0 0) /\ p_w v = w /\ p_h v = h /\ p_d v = d /\ p_data v <> 0 /\ p_cmap v = 0) c
       /\ rt_live RT Σ' = (p_data v, rsize v) :: (pix, 64) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (RASTER_COST + 8) <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixDestroy_rc_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pp pix : Z) (v : pixv) (cv : cmapv) (rc : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pp -> optrL RT (rt_live RT Σ) Σ m pp 8 -> rw_cells asegs m pp [C8 (Z_to_bv 64 pix)] ->
  pix_obj_rc (rt_live RT Σ) m pix v cv rc -> 2 <= rc < 2^31 -> (pp + 8 <= pix \/ pix + 64 <= pp) ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 1 0 1 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixDestroy m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pp, pp + 8); (pix + 20, pix + 24)] m m'
          /\ rw_cells asegs m' pp [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m' pix (pix_cells_rc v (rc - 1))) c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 1 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixCopyInputFormat_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixd pixs : Z) (vd vs : pixv) (cvd cvs : cmapv) (rc : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixd -> a1 = Z_to_bv 64 pixs ->
  pix_obj (rt_live RT Σ) m pixd vd cvd -> pix_obj_rc (rt_live RT Σ) m pixs vs cvs rc -> pixd <> pixs ->
  lenv RT Σ m sp lo (LSTK 1) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCopyInputFormat m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pixd + 32, pixd + 36)] m m'
          /\ rw_cells asegs m' pixd (pix_cells (pv_inf vd vs))) c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ <= rt_credit RT Σ').

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition REMOVE_RAS : list Z :=
  [0x999f4; 0x99a04; 0x99a14; 0x99a4c;          (* [comment removed for export] *)
   0x9bf00;                                      (* [comment removed for export] *)
   0x9d4e8; 0x9d59c; 0x9d5a4; 0x9d5ac; 0x9d5b4]. (* [comment removed for export] *)
Definition pixRemoveColormap_gray_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (cv : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 1 ->
  pix_obj (rt_live RT Σ) m pix v cv -> p_d v = 8 -> p_data v <> 0 -> cmap_nz v cv ->
  uctx m sp s0 ras ->
  (p_cmap v <> 0 -> Forall (fun f => In (f :: bv_unsigned ra :: ras) CLIENT_TRACES \/ In [f] CLIENT_TRACES) REMOVE_RAS) ->
  lenv RT Σ m sp lo (LSTK 8) -> lres RT Σ 4 7 REMOVE_COST ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixRemoveColormap m)))
    (fun c => exists (Σ' : rts RT) (r : Z) (vr : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 r) m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo
          /\ keepsL RT (rt_live RT Σ) Σ sp [(pix + 20, pix + 24)] m m'
          /\ ((p_cmap v = 0 /\ r = pix /\ pix_obj_rc (rt_live RT Σ') m' pix v cv 2)
              \/ (p_cmap v <> 0 /\ pix_obj (rt_live RT Σ') m' pix v cv
                  /\ pix_obj (rt_live RT Σ') m' r vr (mkCmapv 0 0 0 0)
                  /\ p_w vr = p_w v /\ p_h vr = p_h v /\ p_d vr = 8 /\ p_data vr <> 0 /\ p_cmap vr = 0))) c
       /\ (p_cmap v = 0 -> rt_live RT Σ' = rt_live RT Σ)
       /\ (p_cmap v <> 0 -> rt_live RT Σ' = (p_data vr, rsize vr) :: (r, 64) :: rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - REMOVE_COST <= rt_credit RT Σ').

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gq_op_cps (entry ra_fuzz lvl frames chunks : Z) (cost : Z -> Z)
    (ARGS : word -> word -> word -> word -> word -> bvmap 5 word -> Prop) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (cv : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> ARGS a1 a2 a3 a4 a5 F ->
  pix_obj (rt_live RT Σ) m pix v cv -> p_data v <> 0 -> cmap_nz v cv ->
  uctx m sp s0 ras -> bv_unsigned ra = ra_fuzz -> ras = [RA_TOP] ->
  lenv RT Σ m sp lo (LSTK lvl) -> lres RT Σ frames chunks (cost (p_d v)) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc entry m)))
    (fun c => exists (Σ' : rts RT) (r : Z) (vr : pixv) (cvr : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 r) m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [(pix + 20, pix + 24)] m m'
          /\ pix_obj (rt_live RT Σ') m' pix v cv
          /\ (r = 0 \/ (pix_obj (rt_live RT Σ') m' r vr cvr /\ p_data vr <> 0))) c
       /\ (r = 0 -> rt_live RT Σ' = rt_live RT Σ)
       /\ (r <> 0 -> live_destroy r vr cvr (rt_live RT Σ') = rt_live RT Σ)
       /\ (forall p n, In (p, n) (rt_live RT Σ') -> 0 < n)
       /\ Z.of_nat (length (rt_live RT Σ')) <= Z.of_nat (length (rt_live RT Σ)) + 4
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - cost (p_d v) <= rt_credit RT Σ').
Definition wZ (w : word) (z : Z) : Prop := w = Z_to_bv 64 z.

(* [comment removed for export] *)
Definition pixDitherTo2bpp_cps : Prop :=
  gq_op_cps e_pixDitherTo2bpp RA_FUZZ_OP1 11 6 12 D2_COST (fun a1 _ _ _ _ _ => wZ a1 1).
(* [comment removed for export] *)
Definition pixDitherToBinary_cps : Prop :=
  gq_op_cps e_pixDitherToBinary RA_FUZZ_OP2 11 6 12 DBIN_COST (fun _ _ _ _ _ _ => True).
(* [comment removed for export] *)
Definition pixGenerateMaskByBand_cps : Prop :=
  gq_op_cps e_pixGenerateMaskByBand RA_FUZZ_OP3 7 4 2 BAND_COST (fun a1 a2 a3 a4 _ _ => wZ a1 1 /\ wZ a2 2 /\ wZ a3 1 /\ wZ a4 1).
(* [comment removed for export] *)
Definition pixGenerateMaskByBand32_cps : Prop :=
  gq_op_cps e_pixGenerateMaskByBand32 RA_FUZZ_OP4 7 4 2 BAND32_COST
            (fun a1 a2 a3 _ _ F => wZ a1 1 /\ wZ a2 1 /\ wZ a3 1 /\ freg_is F fa0 FZERO_W /\ freg_is F fa1 FZERO_W).
(* [comment removed for export] *)
Definition pixGenerateMaskByDiscr32_cps : Prop :=
  gq_op_cps e_pixGenerateMaskByDiscr32 RA_FUZZ_OP5 7 4 2 DISCR32_COST (fun a1 a2 a3 _ _ _ => wZ a1 10 /\ wZ a2 10 /\ wZ a3 1).
(* [comment removed for export] *)
Definition pixThresholdGrayArb_cps : Prop :=
  gq_op_cps e_pixThresholdGrayArb RA_FUZZ_OP6 11 6 12 THR_COST
            (fun a1 a2 a3 a4 a5 _ => wZ a1 LIT_EDGEVALS /\ wZ a2 8 /\ wZ a3 0 /\ wZ a4 0 /\ wZ a5 0).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ditherToBinaryLow_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (datad w h wpld datas wpls bufs1 bufs2 : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 datad -> s32 a1 w -> s32 a2 h -> s32 a3 wpld -> a4 = Z_to_bv 64 datas -> s32 a5 wpls ->
  a6 = Z_to_bv 64 bufs1 -> a7 = Z_to_bv 64 bufs2 -> t3 = Z_to_bv 64 10 -> t4 = Z_to_bv 64 10 ->
  0 < w <= 20000 -> 0 < h <= 20000 -> wpld = (w + 31) / 32 -> wpls = (w * 8 + 31) / 32 -> 4 * (wpls * h) <= 0x4000000 ->
  chunk (rt_live RT Σ) datad (4 * (wpld * h)) -> chunk (rt_live RT Σ) datas (4 * (wpls * h)) ->
  chunk (rt_live RT Σ) bufs1 (4 * wpls) -> chunk (rt_live RT Σ) bufs2 (4 * wpls) ->
  NoDup [datad; datas; bufs1; bufs2] ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 0 0 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_ditherToBinaryLow m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost RT Σ Σ' m m' sp lo
          /\ keeps RT Σ Σ' sp [(datad, datad + 4 * (wpld * h)); (bufs1, bufs1 + 4 * wpls); (bufs2, bufs2 + 4 * wpls)] m m') c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ <= rt_credit RT Σ').

End GqIface.
