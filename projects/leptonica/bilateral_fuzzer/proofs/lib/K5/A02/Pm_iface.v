(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface D_iface D_defs.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition e_pm_fuzz : Z := 0x9635c.                 (* [comment removed for export] *)
Definition e_boxCreate : Z := 0x8da30.
Definition e_boxDestroy : Z := 0x8dd1c.
Definition e_boxGetGeometry : Z := 0xc08b4.
Definition e_pixCreateTemplateNoInit : Z := 0x9a144.
Definition e_pixCopyColormap : Z := 0x9a864.
Definition e_pixCopy : Z := 0x9b4ec.
Definition e_pixGetColormap : Z := 0x9c670.
Definition e_pixcmapAddColor : Z := 0xa0c80.
Definition e_pixcmapCopy : Z := 0xa139c.
Definition e_pixcmapGetIndex : Z := 0x91cfc.
Definition e_pixcmapGetCount : Z := 0x91f20.
Definition e_pixSetSelectCmap : Z := 0x92d8c.
Definition e_pixSetSelectMaskedCmap : Z := 0x93670.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition box_cells (x y w h : Z) : list cell :=
  [C4 (Z_to_bv 64 x); C4 (Z_to_bv 64 y); C4 (Z_to_bv 64 w); C4 (Z_to_bv 64 h); C4 (Z_to_bv 64 1)].
Definition box_obj (live : list (Z * Z)) (m : mem) (b x y w h : Z) : Prop :=
  rw_cells asegs m b (box_cells x y w h) /\ chunk live b 20.

(* [comment removed for export] *)
Definition pm_copy_live (pixd : Z) (v' : pixv) (cv' : cmapv) (live : list (Z * Z)) : list (Z * Z) :=
  (if p_cmap v' =? 0 then [] else [(c_arr cv', 4 * c_nalloc cv'); (p_cmap v', 24)])
  ++ (p_data v', rsize v') :: (pixd, 64) :: live.
(* [comment removed for export] *)
Definition pm_fp (v : pixv) (cv : cmapv) : list (Z * Z) :=
  (p_data v, p_data v + rsize v)
  :: (if p_cmap v =? 0 then [] else [(p_cmap v, p_cmap v + 24); (c_arr cv, c_arr cv + 4 * c_nalloc cv)]).

Section PmIface.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition boxDestroy_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pp b x y w h : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pp -> optrF RT Σ m pp 8 -> rw_cells asegs m pp [C8 (Z_to_bv 64 b)] -> box_obj (rt_live RT Σ) m b x y w h ->
  lenv RT Σ m sp lo (LSTK 1) -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_boxDestroy m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pp, pp + 8)] m m' /\ rw_cells asegs m' pp [C8 (Z_to_bv 64 0)]) c
       /\ rt_live RT Σ' = live_remove b (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition boxGetGeometry_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (b x y w h px py pw ph : Z) (x0 y0 w0 h0 : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 b -> a1 = Z_to_bv 64 px -> a2 = Z_to_bv 64 py -> a3 = Z_to_bv 64 pw -> a4 = Z_to_bv 64 ph ->
  box_obj (rt_live RT Σ) m b x y w h -> 0 <= x < 2^31 -> 0 <= y < 2^31 -> 0 <= w < 2^31 -> 0 <= h < 2^31 ->
  optrF RT Σ m px 4 -> optrF RT Σ m py 4 -> optrF RT Σ m pw 4 -> optrF RT Σ m ph 4 ->
  px + 4 <= py -> py + 4 <= pw -> pw + 4 <= ph ->
  rw_cells asegs m px [C4 x0] -> rw_cells asegs m py [C4 y0] -> rw_cells asegs m pw [C4 w0] -> rw_cells asegs m ph [C4 h0] ->
  lenv RT Σ m sp lo (LSTK 1) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_boxGetGeometry m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(px, px + 4); (py, py + 4); (pw, pw + 4); (ph, ph + 4)] m m'
          /\ rw_cells asegs m' px [C4 (Z_to_bv 64 x)] /\ rw_cells asegs m' py [C4 (Z_to_bv 64 y)]
          /\ rw_cells asegs m' pw [C4 (Z_to_bv 64 w)] /\ rw_cells asegs m' ph [C4 (Z_to_bv 64 h)]) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pixSetSelectCmap_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix b : Z) (v : pixv) (cv : cmapv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 b -> a2 = Z_to_bv 64 2 -> a3 = Z_to_bv 64 255 -> a4 = Z_to_bv 64 255 -> a5 = Z_to_bv 64 100 ->
  pix_obj (rt_live RT Σ) m pix v cv -> p_data v <> 0 -> box_obj (rt_live RT Σ) m b 278 35 122 50 -> b <> pix ->
  lenv RT Σ m sp lo (LSTK 6) -> lres RT Σ 2 0 4 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixSetSelectCmap m)))
    (fun c => exists (Σ' : rts RT) (rv : word) (cv' : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp (pm_fp v cv) m m'
          /\ pix_obj (rt_live RT Σ') m' pix v cv' /\ c_arr cv' = c_arr cv /\ c_depth cv' = c_depth cv /\ c_nalloc cv' = c_nalloc cv) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - 4 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixSetSelectMaskedCmap_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (cv : cmapv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 0 -> pix_obj (rt_live RT Σ) m pix v cv ->
  lenv RT Σ m sp lo (LSTK 6) -> lres RT Σ 2 0 4 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixSetSelectMaskedCmap m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [] m m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - 4 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition PM_FUZZ_LIVE : Z := 16.
Definition pm_fuzz_one_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d : Z) (bs : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (Z.of_nat (length bs)) -> tp = Z_to_bv 64 TP_A -> bv_unsigned ra = RA_TOP ->
  0 < d -> Z.of_nat (length bs) < 2^26 -> bytes_at asegs m d bs ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n /\ d mod 8 = 0) \/ bs = []) ->
  rt_frames RT Σ = [] -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  Z.of_nat (length (rt_live RT Σ)) + PM_FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ ->
  (bv_unsigned s0 < bv_unsigned sp \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->
  LIB m -> io_ssp m -> ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= rt_sp0 RT Σ ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_pm_fuzz m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) LIB_FP m m' /\ LIB m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = [] /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - FUZZ_COST <= rt_credit RT Σ').

End PmIface.
