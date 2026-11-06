(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit D_iface D_defs Lept_iface LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_stringReplace : Z := 0x917fc.
Definition e_pixCreateTemplate : Z := 0x9298c.
Definition e_pixCreateTemplateNoInit : Z := 0x92b24.
Definition e_pixCopySpp : Z := 0x93108.
Definition e_pixCopyResolution : Z := 0x932b8.
Definition e_pixCopyColormap : Z := 0x9345c.
Definition e_pixCopy : Z := 0x943b4.
Definition e_pixGetColormap : Z := 0x95450.
Definition e_pixGetSpp : Z := 0x955b4.
Definition e_pixAddBorderGeneral : Z := 0x96d24.
Definition e_pixRemoveBorderGeneral : Z := 0x97308.
Definition e_pixcmapCopy : Z := 0x99320.
Definition e_pixRasterop : Z := 0xa2280.
Definition e_rasteropUniLow : Z := 0xa275c.
Definition e_rasteropLow : Z := 0xa3328.

(* [comment removed for export] *)
Definition GM_RMASK32 : Z := 0x263c0.
Definition GM_LMASK32 : Z := 0x26480.

(* [comment removed for export] *)
Definition RA_NOINIT_MALLOC : Z := 0x91dc8.      (* [comment removed for export] *)
Definition RA_CMAPCOPY_CALLOC1 : Z := 0x99374.   (* [comment removed for export] *)
Definition RA_CMAPCOPY_CALLOC2 : Z := 0x993a4.   (* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition TEMPLATE_COST : Z := RASTER_COST + 16.
Definition BORDER_COST : Z := RASTER_COST + 32.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition hdr_args_ok (w h d : Z) : Prop :=
  In d [1; 2; 4; 8; 16; 24; 32] /\ 0 < w <= 20000 /\ 0 < h <= 20000 /\ 0 < 4 * (((w * d + 31) / 32) * h) <= 0x4000000.

Section GmIface.
Variable RT : rt_sig.

(* [comment removed for export] *)
Record gm_gaps : Prop := mkGmGaps {
  gm_acc_rmask32 : forall Σ m, ART RT Σ m -> acc asegs m GM_RMASK32 132;
  gm_acc_lmask32 : forall Σ m, ART RT Σ m -> acc asegs m GM_LMASK32 132
}.

(* [comment removed for export] *)
Definition optrV (Σ : rts RT) (m : mem) (sp : word) (p : Z) : Prop :=
  optrF RT Σ m p 4 \/ (bv_unsigned sp <= p /\ p + 4 <= USTACK_TOP - 16 /\ p mod 4 = 0).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pixcmapIsValid_null_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (cmap pv : Z) (cv : cmapv) (x : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 cmap -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 pv -> cmap_obj (rt_live RT Σ) m cmap cv ->
  optrV Σ m sp pv -> rw_cells asegs m pv [C4 x] ->
  lenv RT Σ m sp lo (LSTK 2) -> lres RT Σ 1 0 1 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixcmapIsValid m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pv, pv + 4)] m m' /\ rw_cells asegs m' pv [C4 (Z_to_bv 64 1)]) c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 1 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixDestroy_null_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pp : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pp -> optrL RT (rt_live RT Σ) Σ m pp 8 -> rw_cells asegs m pp [C8 (Z_to_bv 64 0)] ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 1 0 1 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixDestroy m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [] m m') c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 1 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixCreateHeader_sure_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (w h d : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  s32 a0 w -> s32 a1 h -> s32 a2 d -> hdr_args_ok w h d ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 0 1 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCreateHeader m)))
    (fun c => exists (Σ' : rts RT) (pix : Z) (v : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pix) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix_obj (rt_live RT Σ') m' pix v (mkCmapv 0 0 0 0) /\ p_w v = w /\ p_h v = h /\ p_d v = d /\ p_data v = 0 /\ p_cmap v = 0) c
       /\ rt_live RT Σ' = (pix, 64) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixCreateNoInit_sure_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (w h d : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  s32 a0 w -> s32 a1 h -> s32 a2 d -> hdr_args_ok w h d ->
  uctx m sp s0 ras -> In (RA_NOINIT_MALLOC :: bv_unsigned ra :: ras) CLIENT_TRACES ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 3 2 (RASTER_COST + 4) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCreateNoInit m)))
    (fun c => exists (Σ' : rts RT) (pix : Z) (v : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pix) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix_obj (rt_live RT Σ') m' pix v (mkCmapv 0 0 0 0) /\ p_w v = w /\ p_h v = h /\ p_d v = d /\ p_data v <> 0 /\ p_cmap v = 0) c
       /\ rt_live RT Σ' = (p_data v, rsize v) :: (pix, 64) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (RASTER_COST + 4) <= rt_credit RT Σ').

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stringReplace_null_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pd : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pd -> a1 = Z_to_bv 64 0 -> optrL RT (rt_live RT Σ) Σ m pd 8 -> rw_cells asegs m pd [C8 (Z_to_bv 64 0)] ->
  lenv RT Σ m sp lo (LSTK 1) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_stringReplace m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pd, pd + 8)] m m' /\ rw_cells asegs m' pd [C8 (Z_to_bv 64 0)]) c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixcmapCopy_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (cmaps : Z) (cvs : cmapv) (ra1 : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 cmaps -> cmap_obj (rt_live RT Σ) m cmaps cvs ->
  uctx m sp s0 (ra1 :: ras) -> In (RA_CMAPCOPY_CALLOC1 :: ra1 :: ras) CLIENT_TRACES ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 1 2 1 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixcmapCopy m)))
    (fun c => exists (Σ' : rts RT) (cmapd : Z) (cvd : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 cmapd) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ cmap_obj (rt_live RT Σ') m' cmapd cvd /\ c_depth cvd = c_depth cvs /\ c_nalloc cvd = c_nalloc cvs /\ c_n cvd = c_n cvs) c
       /\ rt_live RT Σ' = (c_arr cvd, 4 * c_nalloc cvd) :: (cmapd, 24) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 1 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixCopyColormap_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixd pixs : Z) (vd vs : pixv) (cvd cvs : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixd -> a1 = Z_to_bv 64 pixs ->
  pix_obj (rt_live RT Σ) m pixd vd cvd -> pix_obj (rt_live RT Σ) m pixs vs cvs -> pixd <> pixs -> p_d vd = p_d vs -> p_cmap vd = 0 ->
  (p_cmap vs <> 0 -> uctx m sp s0 ras /\ In (RA_CMAPCOPY_CALLOC1 :: bv_unsigned ra :: ras) CLIENT_TRACES) ->
  lenv RT Σ m sp lo (LSTK 7) -> lres RT Σ 2 2 4 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCopyColormap m)))
    (fun c => exists (Σ' : rts RT) (rv : word) (cmapd : Z) (cvn : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [(pixd + 48, pixd + 56)] m m'
          /\ rw_cells asegs m' pixd (pix_cells (mkPixv (p_w vd) (p_h vd) (p_d vd) (p_spp vd) (p_wpl vd) (p_xres vd) (p_yres vd) (p_inf vd) (p_spec vd) cmapd (p_data vd)))
          /\ (cmapd = 0 \/ (cmap_obj (rt_live RT Σ') m' cmapd cvn /\ c_depth cvn = c_depth cvs))) c
       /\ (p_cmap vs = 0 -> cmapd = 0) /\ (p_cmap vs <> 0 -> cmapd <> 0)
       /\ rt_live RT Σ' = (if cmapd =? 0 then rt_live RT Σ else (c_arr cvn, 4 * c_nalloc cvn) :: (cmapd, 24) :: rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 4 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixCreateTemplateNoInit_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs : Z) (vs : pixv) (cvs : cmapv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixs -> pix_obj (rt_live RT Σ) m pixs vs cvs ->
  lenv RT Σ m sp lo (LSTK 8) -> lres RT Σ 3 4 TEMPLATE_COST ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCreateTemplateNoInit m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv) (cvd : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix_obj (rt_live RT Σ') m' pixd vd cvd /\ p_w vd = p_w vs /\ p_h vd = p_h vs /\ p_d vd = p_d vs /\ p_data vd <> 0) c
       /\ (p_cmap vs = 0 -> p_cmap vd = 0 /\ rt_live RT Σ' = (p_data vd, rsize vd) :: (pixd, 64) :: rt_live RT Σ)
       /\ live_destroy pixd vd cvd (rt_live RT Σ') = rt_live RT Σ
       /\ (forall p n, In (p, n) (rt_live RT Σ') -> 0 < n) /\ Z.of_nat (length (rt_live RT Σ')) <= Z.of_nat (length (rt_live RT Σ)) + 4
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - TEMPLATE_COST <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixCreateTemplate_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs : Z) (vs : pixv) (cvs : cmapv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixs -> pix_obj (rt_live RT Σ) m pixs vs cvs -> p_data vs <> 0 ->
  lenv RT Σ m sp lo (LSTK 9) -> lres RT Σ 3 4 TEMPLATE_COST ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCreateTemplate m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv) (cvd : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix_obj (rt_live RT Σ') m' pixd vd cvd /\ p_w vd = p_w vs /\ p_h vd = p_h vs /\ p_d vd = p_d vs /\ p_data vd <> 0) c
       /\ (p_cmap vs = 0 -> p_cmap vd = 0 /\ rt_live RT Σ' = (p_data vd, rsize vd) :: (pixd, 64) :: rt_live RT Σ)
       /\ live_destroy pixd vd cvd (rt_live RT Σ') = rt_live RT Σ
       /\ (forall p n, In (p, n) (rt_live RT Σ') -> 0 < n) /\ Z.of_nat (length (rt_live RT Σ')) <= Z.of_nat (length (rt_live RT Σ)) + 4
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - TEMPLATE_COST <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixCopy_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs : Z) (vs : pixv) (cvs : cmapv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 0 -> a1 = Z_to_bv 64 pixs -> pix_obj (rt_live RT Σ) m pixs vs cvs -> p_data vs <> 0 ->
  lenv RT Σ m sp lo (LSTK 9) -> lres RT Σ 3 4 TEMPLATE_COST ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCopy m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv) (cvd : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix_obj (rt_live RT Σ') m' pixd vd cvd /\ p_w vd = p_w vs /\ p_h vd = p_h vs /\ p_d vd = p_d vs /\ p_data vd <> 0) c
       /\ (p_cmap vs = 0 -> p_cmap vd = 0 /\ rt_live RT Σ' = (p_data vd, rsize vd) :: (pixd, 64) :: rt_live RT Σ)
       /\ live_destroy pixd vd cvd (rt_live RT Σ') = rt_live RT Σ
       /\ (forall p n, In (p, n) (rt_live RT Σ') -> 0 < n) /\ Z.of_nat (length (rt_live RT Σ')) <= Z.of_nat (length (rt_live RT Σ)) + 4
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - TEMPLATE_COST <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixCopyResolution_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixd pixs : Z) (vd vs : pixv) (cvd cvs : cmapv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixd -> a1 = Z_to_bv 64 pixs ->
  pix_obj (rt_live RT Σ) m pixd vd cvd -> pix_obj (rt_live RT Σ) m pixs vs cvs -> pixd <> pixs ->
  lenv RT Σ m sp lo (LSTK 1) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCopyResolution m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pixd + 24, pixd + 32)] m m'
          /\ rw_cells asegs m' pixd (pix_cells (mkPixv (p_w vd) (p_h vd) (p_d vd) (p_spp vd) (p_wpl vd) (p_xres vs) (p_yres vs) (p_inf vd) (p_spec vd) (p_cmap vd) (p_data vd)))) c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ <= rt_credit RT Σ').

Definition pixCopySpp_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixd pixs : Z) (vd vs : pixv) (cvd cvs : cmapv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixd -> a1 = Z_to_bv 64 pixs ->
  pix_obj (rt_live RT Σ) m pixd vd cvd -> pix_obj (rt_live RT Σ) m pixs vs cvs -> pixd <> pixs ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 1 0 1 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCopySpp m)))
    (fun c => exists (Σ' : rts RT) (rv : word) (spp : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pixd + 12, pixd + 16)] m m'
          /\ rw_cells asegs m' pixd (pix_cells (mkPixv (p_w vd) (p_h vd) (p_d vd) spp (p_wpl vd) (p_xres vd) (p_yres vd) (p_inf vd) (p_spec vd) (p_cmap vd) (p_data vd)))) c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 1 <= rt_credit RT Σ').

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition raster8 (live : list (Z * Z)) (data w h wpl : Z) : Prop :=
  chunk live data (4 * (wpl * h)) /\ 0 < w <= 20000 /\ 0 < h <= 20000 /\ wpl = (w * 8 + 31) / 32 /\ 4 * (wpl * h) <= 0x4000000.
(* [comment removed for export] *)
Definition rect_in (x y rw rh w h : Z) : Prop := 0 <= x /\ 0 <= y /\ 0 < rw /\ 0 < rh /\ x + rw <= w /\ y + rh <= h.

(* [comment removed for export] *)
Definition rasteropUniLow_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (datad w h wpl dx dy dw dh op : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 datad -> a1 = Z_to_bv 64 w -> a2 = Z_to_bv 64 h -> a3 = Z_to_bv 64 8 -> a4 = Z_to_bv 64 wpl ->
  a5 = Z_to_bv 64 dx -> a6 = Z_to_bv 64 dy -> a7 = Z_to_bv 64 dw ->
  rw_cells asegs m (bv_unsigned sp) [C8 (Z_to_bv 64 dh); C8 (Z_to_bv 64 op)] -> (op = 0 \/ op = 15) ->
  raster8 (rt_live RT Σ) datad w h wpl -> rect_in dx dy dw dh w h ->
  lenv RT Σ m sp lo (LSTK 1) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_rasteropUniLow m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(datad, datad + 4 * (wpl * h))] m m') c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition rasteropLow_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (datad dpw dph dwpl dx dy dw dh datas spw sph swpl sx sy : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 datad -> a1 = Z_to_bv 64 dpw -> a2 = Z_to_bv 64 dph -> a3 = Z_to_bv 64 8 -> a4 = Z_to_bv 64 dwpl ->
  a5 = Z_to_bv 64 dx -> a6 = Z_to_bv 64 dy -> a7 = Z_to_bv 64 dw ->
  rw_cells asegs m (bv_unsigned sp) [C8 (Z_to_bv 64 dh); C8 (Z_to_bv 64 12); C8 (Z_to_bv 64 datas); C8 (Z_to_bv 64 spw);
                                     C8 (Z_to_bv 64 sph); C8 (Z_to_bv 64 swpl); C8 (Z_to_bv 64 sx); C8 (Z_to_bv 64 sy)] ->
  raster8 (rt_live RT Σ) datad dpw dph dwpl -> raster8 (rt_live RT Σ) datas spw sph swpl -> datad <> datas ->
  rect_in dx dy dw dh dpw dph -> rect_in sx sy dw dh spw sph -> dx mod 4 = 0 -> sx mod 4 = 0 ->
  lenv RT Σ m sp lo (LSTK 1) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_rasteropLow m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(datad, datad + 4 * (dwpl * dph))] m m') c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixRasterop_uni_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixd : Z) (vd : pixv) (cvd : cmapv) (dx dy dw dh op : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixd -> a1 = Z_to_bv 64 dx -> a2 = Z_to_bv 64 dy -> a3 = Z_to_bv 64 dw -> a4 = Z_to_bv 64 dh -> a5 = Z_to_bv 64 op ->
  (op = 0 \/ op = 15) -> pix_obj (rt_live RT Σ) m pixd vd cvd -> p_d vd = 8 -> p_data vd <> 0 ->
  rect_in dx dy dw dh (p_w vd) (p_h vd) ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 1 0 1 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixRasterop m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(p_data vd, p_data vd + rsize vd)] m m') c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 1 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixRasterop_src_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixd pixs : Z) (vd vs : pixv) (cvd cvs : cmapv) (dx dy dw dh sx sy : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixd -> a1 = Z_to_bv 64 dx -> a2 = Z_to_bv 64 dy -> a3 = Z_to_bv 64 dw -> a4 = Z_to_bv 64 dh -> a5 = Z_to_bv 64 12 ->
  a6 = Z_to_bv 64 pixs -> a7 = Z_to_bv 64 sx -> rw_cells asegs m (bv_unsigned sp) [C8 (Z_to_bv 64 sy)] ->
  pix_obj (rt_live RT Σ) m pixd vd cvd -> p_d vd = 8 -> p_data vd <> 0 ->
  pix_obj (rt_live RT Σ) m pixs vs cvs -> p_d vs = 8 -> p_data vs <> 0 -> pixd <> pixs -> p_data vd <> p_data vs ->
  rect_in dx dy dw dh (p_w vd) (p_h vd) -> rect_in sx sy dw dh (p_w vs) (p_h vs) -> dx mod 4 = 0 -> sx mod 4 = 0 ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 1 0 1 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixRasterop m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(p_data vd, p_data vd + rsize vd)] m m') c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 1 <= rt_credit RT Σ').

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition new_pix8 (Σ Σ' : rts RT) (m' : mem) (r w h : Z) (v : pixv) : Prop :=
  (r = 0 \/ (pix_obj (rt_live RT Σ') m' r v (mkCmapv 0 0 0 0) /\ p_w v = w /\ p_h v = h /\ p_d v = 8 /\ p_data v <> 0 /\ p_cmap v = 0)).
Definition new_pix8_live (Σ Σ' : rts RT) (r : Z) (v : pixv) : Prop :=
  rt_live RT Σ' = (if r =? 0 then rt_live RT Σ else (p_data v, rsize v) :: (r, 64) :: rt_live RT Σ).

(* [comment removed for export] *)
Definition pixAddBorderGeneral_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs : Z) (vs : pixv) (cvs : cmapv) (val : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixs -> a1 = Z_to_bv 64 4 -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 2 -> a4 = Z_to_bv 64 8 -> a5 = Z_to_bv 64 val ->
  (val = 0 \/ val = 255) -> pix_obj (rt_live RT Σ) m pixs vs cvs -> p_d vs = 8 -> p_cmap vs = 0 -> p_data vs <> 0 ->
  lenv RT Σ m sp lo (LSTK 8) -> lres RT Σ 4 4 BORDER_COST ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixAddBorderGeneral m)))
    (fun c => exists (Σ' : rts RT) (r : Z) (v : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 r) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m' /\ new_pix8 Σ Σ' m' r (p_w vs + 12) (p_h vs + 10) v) c
       /\ new_pix8_live Σ Σ' r v
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - BORDER_COST <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixRemoveBorderGeneral_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs : Z) (vs : pixv) (cvs : cmapv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixs -> a1 = Z_to_bv 64 4 -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 2 -> a4 = Z_to_bv 64 8 ->
  pix_obj (rt_live RT Σ) m pixs vs cvs -> p_d vs = 8 -> p_cmap vs = 0 -> p_data vs <> 0 -> 12 < p_w vs -> 10 < p_h vs ->
  lenv RT Σ m sp lo (LSTK 8) -> lres RT Σ 4 4 BORDER_COST ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixRemoveBorderGeneral m)))
    (fun c => exists (Σ' : rts RT) (r : Z) (v : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 r) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m' /\ new_pix8 Σ Σ' m' r (p_w vs - 12) (p_h vs - 10) v) c
       /\ new_pix8_live Σ Σ' r v
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - BORDER_COST <= rt_credit RT Σ').

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
End GmIface.

(* [comment removed for export] *)