(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import ImageA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import Layout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Pm_iface D_iface D_defs.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition cmapv_n (cv : cmapv) (n' : Z) : cmapv := mkCmapv (c_arr cv) (c_depth cv) (c_nalloc cv) n'.

Section PmIface2.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition pixcmapGetIndex_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (cmap pi : Z) (cv : cmapv) (x : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 cmap -> a4 = Z_to_bv 64 pi -> cmap_obj (rt_live RT Σ) m cmap cv -> optrF RT Σ m pi 4 -> rw_cells asegs m pi [C4 x] ->
  lenv RT Σ m sp lo (LSTK 2) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixcmapGetIndex m)))
    (fun c => exists (Σ' : rts RT) (rv i : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 rv) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pi, pi + 4)] m m' /\ rw_cells asegs m' pi [C4 (Z_to_bv 64 i)]
          /\ ((rv = 0 /\ 0 <= i < c_n cv) \/ (rv = 1 /\ i = 0))) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition pixcmapAddColor_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (cmap : Z) (cv : cmapv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 cmap -> cmap_obj (rt_live RT Σ) m cmap cv ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 1 0 1 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixcmapAddColor m)))
    (fun c => exists (Σ' : rts RT) (rv : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 rv) m' ms
          /\ lpost RT Σ Σ' m m' sp lo
          /\ keeps RT Σ Σ' sp [(cmap + 16, cmap + 20); (c_arr cv, c_arr cv + 4 * c_nalloc cv)] m m'
          /\ ((rv = 0 /\ c_n cv < c_nalloc cv /\ cmap_obj (rt_live RT Σ') m' cmap (cmapv_n cv (c_n cv + 1)))
              \/ (rv = 1 /\ c_n cv = c_nalloc cv /\ cmap_obj (rt_live RT Σ') m' cmap cv))) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - 1 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixcmapIsValid_stk_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (cmap pv : Z) (cv : cmapv) (x : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 cmap -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 pv -> cmap_obj (rt_live RT Σ) m cmap cv ->
  bv_unsigned sp <= pv -> pv + 4 <= USTACK_TOP - 16 -> pv mod 4 = 0 -> rw_cells asegs m pv [C4 x] ->
  lenv RT Σ m sp lo (LSTK 5) -> lres RT Σ 2 0 4 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixcmapIsValid m)))
    (fun c => exists (Σ' : rts RT) (rv y : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pv, pv + 4)] m m' /\ rw_cells asegs m' pv [C4 y]) c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 4 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition PMCOPY_CALLOC1 : Z := 0x91db8.
Definition PMCOPY_CALLOC2 : Z := 0x91de8.
Definition pixcmapCopy_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (cmaps : Z) (cv : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 cmaps -> cmap_obj (rt_live RT Σ) m cmaps cv ->
  uctx m sp s0 ras -> (ras = [] -> bv_unsigned s0 <= lo \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->
  In (PMCOPY_CALLOC1 :: ras) CLIENT_TRACES ->
  lenv RT Σ m sp lo (LSTK 6) -> lres RT Σ 2 2 6 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixcmapCopy m)))
    (fun c => exists (Σ' : rts RT) (cmapd : Z) (cv' : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 cmapd) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ (cmapd <> 0 -> cmap_obj (rt_live RT Σ') m' cmapd cv' /\ c_depth cv' = c_depth cv /\ c_nalloc cv' = c_nalloc cv /\ c_n cv' = c_n cv)) c
       /\ rt_live RT Σ' = (if cmapd =? 0 then rt_live RT Σ else (c_arr cv', 4 * c_nalloc cv') :: (cmapd, 24) :: rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 6 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixv_cmap (v : pixv) (c : Z) : pixv :=
  mkPixv (p_w v) (p_h v) (p_d v) (p_spp v) (p_wpl v) (p_xres v) (p_yres v) (p_inf v) (p_spec v) c (p_data v).
Definition pixCopyColormap_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixd pixs : Z) (vd v : pixv) (cv : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixd -> a1 = Z_to_bv 64 pixs -> pix_obj (rt_live RT Σ) m pixs v cv ->
  pix_obj (rt_live RT Σ) m pixd vd (mkCmapv 0 0 0 0) -> p_cmap vd = 0 -> p_data vd <> 0 -> p_d vd = p_d v -> pixd <> pixs ->
  uctx m sp s0 ras -> In (PMCOPY_CALLOC1 :: bv_unsigned ra :: ras) CLIENT_TRACES ->
  lenv RT Σ m sp lo (LSTK 7) -> lres RT Σ 3 2 16 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCopyColormap m)))
    (fun c => exists (Σ' : rts RT) (rv : word) (cmapd : Z) (cv' : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [(pixd + 48, pixd + 56)] m m'
          /\ pix_obj (rt_live RT Σ') m' pixd (pixv_cmap vd cmapd) cv'
          /\ (cmapd <> 0 -> p_cmap v <> 0 /\ c_depth cv' = c_depth cv /\ c_nalloc cv' = c_nalloc cv /\ c_n cv' = c_n cv)) c
       /\ rt_live RT Σ' = (if cmapd =? 0 then rt_live RT Σ else (c_arr cv', 4 * c_nalloc cv') :: (cmapd, 24) :: rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 16 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition e_stringReplace : Z := 0x8de48.
Definition stringReplace_null_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pd : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pd -> a1 = Z_to_bv 64 0 -> optr RT Σ m pd 8 -> rw_cells asegs m pd [C8 (Z_to_bv 64 0)] ->
  lenv RT Σ m sp lo (LSTK 1) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_stringReplace m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pd, pd + 8)] m m' /\ rw_cells asegs m' pd [C8 (Z_to_bv 64 0)]) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition pixCreateNoInit_cps (entry msite : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (w h d : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  s32 a0 w -> s32 a1 h -> s32 a2 d ->
  uctx m sp s0 ras -> In (msite :: bv_unsigned ra :: ras) CLIENT_TRACES ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 3 2 (RASTER_COST + 8) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc entry m)))
    (fun c => exists (Σ' : rts RT) (pix : Z) (v : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pix) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ (pix = 0 \/ (pix_obj (rt_live RT Σ') m' pix v (mkCmapv 0 0 0 0) /\ p_w v = w /\ p_h v = h /\ p_d v = d /\ p_data v <> 0 /\ p_cmap v = 0))) c
       /\ rt_live RT Σ' = (if pix =? 0 then rt_live RT Σ else (p_data v, rsize v) :: (pix, 64) :: rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (RASTER_COST + 8) <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition PM_NOINIT_MALLOC : Z := 0x8e8dc.      (* [comment removed for export] *)
Definition RA_TMPL_NOINIT : Z := 0x8f51c.
Definition RA_TMPL_COPYCMAP : Z := 0x8f6b8.
Definition pm_hdr_copy (v v' : pixv) (cv cv' : cmapv) : Prop :=
  p_w v' = p_w v /\ p_h v' = p_h v /\ p_d v' = p_d v /\ p_wpl v' = p_wpl v /\ p_data v' <> 0 /\ (p_cmap v = 0 -> p_cmap v' = 0)
  /\ (p_cmap v' <> 0 -> c_depth cv' = c_depth cv /\ c_nalloc cv' = c_nalloc cv /\ c_n cv' = c_n cv).
Definition pixCreateTemplateNoInit_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs : Z) (v : pixv) (cv : cmapv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixs -> pix_obj (rt_live RT Σ) m pixs v cv ->
  lenv RT Σ m sp lo (LSTK 8) -> lres RT Σ 3 4 (RASTER_COST + 32) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCreateTemplateNoInit m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (v' : pixv) (cv' : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ (pixd <> 0 -> pix_obj (rt_live RT Σ') m' pixd v' cv' /\ pm_hdr_copy v v' cv cv')) c
       /\ rt_live RT Σ' = (if pixd =? 0 then rt_live RT Σ else pm_copy_live pixd v' cv' (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - (RASTER_COST + 32) <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixCopy_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs : Z) (v : pixv) (cv : cmapv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 0 -> a1 = Z_to_bv 64 pixs -> pix_obj (rt_live RT Σ) m pixs v cv -> p_data v <> 0 ->
  lenv RT Σ m sp lo (LSTK 9) -> lres RT Σ 3 4 (RASTER_COST + 64) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCopy m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (v' : pixv) (cv' : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ (pixd <> 0 -> pix_obj (rt_live RT Σ') m' pixd v' cv' /\ pm_hdr_copy v v' cv cv')) c
       /\ rt_live RT Σ' = (if pixd =? 0 then rt_live RT Σ else pm_copy_live pixd v' cv' (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - (RASTER_COST + 64) <= rt_credit RT Σ').

End PmIface2.
