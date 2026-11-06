(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA Arr FP.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Km_setelem Km_iface Pm_iface Pm_iface2 Pm_iface4 Cf_iface RT_fk Bi_iface D_iface D_defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section BiIface2.
Variable RT : rt_sig.

Definition pixRasterop_cps2 : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pd ps : Z) (vd vs : pixv) (dx dy dw dh op sx sy rcs : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pd -> s32 a1 dx -> s32 a2 dy -> s32 a3 dw -> s32 a4 dh -> a5 = Z_to_bv 64 op -> a6 = Z_to_bv 64 ps -> s32 a7 sx ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp) [C8 (Z_to_bv 64 sy)] -> 0 <= sy < 2^31 ->
  (pd = 0 \/ (pix8 (rt_live RT Σ) m pd vd /\ rect_ok vd dx dy dw dh)) ->
  ((op = PIX_CLR /\ ps = 0)
   \/ (op = PIX_SRC /\ pix8rc (rt_live RT Σ) m ps vs rcs /\ 1 <= rcs <= 2 /\ rect_ok vs sx sy dw dh /\ (ps = pd -> vs = vd /\ rcs = 1))) ->
  (op = PIX_SRC -> (dx - sx) mod 4 = 0 -> dx mod 4 = 0) ->
  (* [comment removed for export] *)
  (op = PIX_SRC -> ps <> pd -> ps <> p_data vd) ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 5 0 8 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixRasterop m)))
    (fun c => exists (Σ' : rts RT) (rv : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 rv) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo
          /\ keeps RT Σ Σ' sp (if pd =? 0 then [] else [(p_data vd, p_data vd + rsize vd)]) m m'
          /\ (pd <> 0 -> pix8 (rt_live RT Σ') m' pd vd) /\ (op = PIX_SRC -> pix8rc (rt_live RT Σ') m' ps vs rcs)) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - 8 <= rt_credit RT Σ').

Definition pixAddBorderGeneral0_cps2 : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (l r t b rc : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 r -> a3 = Z_to_bv 64 t -> a4 = Z_to_bv 64 b -> a5 = Z_to_bv 64 0 ->
  pix_obj_rc (rt_live RT Σ) m pix v (mkCmapv 0 0 0 0) rc -> 1 <= rc <= 2 -> p_d v = 8 -> p_cmap v = 0 -> p_data v <> 0 ->
  1 <= l <= 21 -> 1 <= r <= 21 -> 1 <= t <= 21 -> 1 <= b <= 21 ->
  uctx m sp s0 ras -> In (PMCOPY_CALLOC1 :: 0x9effc :: bv_unsigned ra :: ras) CLIENT_TRACES ->
  lenv RT Σ m sp lo (LSTK 8) -> lres RT Σ 6 4 (RASTER_COST + 72) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixAddBorderGeneral m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix_obj_rc (rt_live RT Σ') m' pix v (mkCmapv 0 0 0 0) rc
          /\ (pixd <> 0 -> pix8 (rt_live RT Σ') m' pixd vd /\ p_w vd = p_w v + l + r /\ p_h vd = p_h v + t + b)) c
       /\ rt_live RT Σ' = (if pixd =? 0 then rt_live RT Σ else pix_new_live pixd vd (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (RASTER_COST + 72) <= rt_credit RT Σ').

Definition pixAddMirroredBorder_cps2 : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (l r t b rc : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 r -> a3 = Z_to_bv 64 t -> a4 = Z_to_bv 64 b ->
  pix_obj_rc (rt_live RT Σ) m pix v (mkCmapv 0 0 0 0) rc -> 1 <= rc <= 2 -> p_d v = 8 -> p_cmap v = 0 -> p_data v <> 0 ->
  1 <= l <= 21 -> 1 <= r <= 21 -> 1 <= t <= 21 -> 1 <= b <= 21 -> l <= p_w v -> r <= p_w v -> t <= p_h v -> b <= p_h v ->
  uctx m sp s0 ras -> In (PMCOPY_CALLOC1 :: 0x9effc :: 0x9f4c8 :: bv_unsigned ra :: ras) CLIENT_TRACES ->
  lenv RT Σ m sp lo (LSTK 9) -> lres RT Σ 7 4 (RASTER_COST + 1024) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixAddMirroredBorder m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix_obj_rc (rt_live RT Σ') m' pix v (mkCmapv 0 0 0 0) rc
          /\ (pixd <> 0 -> pix8 (rt_live RT Σ') m' pixd vd /\ p_w vd = p_w v + l + r /\ p_h vd = p_h v + t + b)) c
       /\ rt_live RT Σ' = (if pixd =? 0 then rt_live RT Σ else pix_new_live pixd vd (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (RASTER_COST + 1024) <= rt_credit RT Σ').

Definition RA_BC_DESTROY : Z := 0xc2ea4.
Definition RA_BC_AMB : Z := 0xc29e4.
Definition bilateralCreate_cps2 : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 10 -> a2 = Z_to_bv 64 1 ->
  reg_get F r_fa0 = fs32 F_5_0 -> reg_get F r_fa1 = fs32 F_10_0 ->
  pix8 (rt_live RT Σ) m pix v -> 22 <= p_w v -> 22 <= p_h v ->
  uctx m sp s0 ras -> Forall (fun f => In (f :: bv_unsigned ra :: ras) CLIENT_TRACES) BC_CALLOC_RAS ->
  In (PIXA_CALLOC1 :: bv_unsigned ra :: ras) CLIENT_TRACES ->   (* [comment removed for export] *)
  In (PGLP_CALLOC :: RA_BC_LINEPTRS :: bv_unsigned ra :: ras) CLIENT_TRACES ->
  Forall (fun f => In (f :: RA_BC_DESTROY :: bv_unsigned ra :: ras) CLIENT_TRACES) DESTROY_FREE_RAS ->
  In (PMCOPY_CALLOC1 :: 0x9effc :: 0x9f4c8 :: RA_BC_AMB :: bv_unsigned ra :: ras) CLIENT_TRACES ->
  lenv RT Σ m sp lo (LSTK 10) -> lres RT Σ 9 48 BC_COST ->
  sec_bytes (rt_live RT Σ) + BC_SECB <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_bilateralCreate m)))
    (fun c => exists (Σ' : rts RT) (bil : Z) (b : bilv) (vsc : pixv) (ps : list pixe) (lps : list Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 bil) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [(pix + 20, pix + 24)] m m'
          /\ (bil = 0 -> pix8 (rt_live RT Σ') m' pix v)
          /\ (bil <> 0 -> b_pixs b = pix /\ bil_obj (rt_live RT Σ') m' bil b v vsc ps lps)) c
       /\ rt_live RT Σ' = (if bil =? 0 then rt_live RT Σ else bil_live bil b vsc ps lps (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - BC_COST <= rt_credit RT Σ').

Definition RA_BGE_DESTROY : Z := 0xc4bf8.
Definition RA_BGE_AMB : Z := 0xc47b4.
Definition pixBilateralGrayExact_cps2 : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (ks datas kr datar : Z) (rowss rowsr : list Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 ks -> a2 = Z_to_bv 64 kr ->
  pix8 (rt_live RT Σ) m pix v -> kel_obj (rt_live RT Σ) m ks 41 41 20 20 datas rowss -> kel_obj (rt_live RT Σ) m kr 1 256 0 0 datar rowsr ->
  uctx m sp s0 ras -> Forall (fun f => In (f :: RA_BGE_DESTROY :: bv_unsigned ra :: ras) CLIENT_TRACES) DESTROY_FREE_RAS ->
  In (PMCOPY_CALLOC1 :: 0x9effc :: 0x9f4c8 :: RA_BGE_AMB :: bv_unsigned ra :: ras) CLIENT_TRACES ->
  lenv RT Σ m sp lo (LSTK 10) -> lres RT Σ 8 50 (3 * RASTER_COST + 2^20) ->
  sec_bytes (rt_live RT Σ) + 2 * 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixBilateralGrayExact m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix8 (rt_live RT Σ') m' pix v /\ kel_obj (rt_live RT Σ') m' ks 41 41 20 20 datas rowss
          /\ kel_obj (rt_live RT Σ') m' kr 1 256 0 0 datar rowsr
          /\ (pixd <> 0 -> pix8 (rt_live RT Σ') m' pixd vd /\ p_w vd = p_w v /\ p_h vd = p_h v)) c
       /\ rt_live RT Σ' = (if pixd =? 0 then rt_live RT Σ else pix_new_live pixd vd (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (3 * RASTER_COST + 2^20) <= rt_credit RT Σ').

Definition pixCreate_nn_cpsF : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (w h d : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  s32 a0 w -> s32 a1 h -> s32 a2 d -> hdr_args_ok w h d ->
  lenv RT Σ m sp lo (LSTK 5) -> lres RT Σ 3 2 (RASTER_COST + 8) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCreate m)))
    (fun c => exists (Σ' : rts RT) (pix : Z) (v : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pix) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix <> 0 /\ pix_obj (rt_live RT Σ') m' pix v (mkCmapv 0 0 0 0) /\ p_w v = w /\ p_h v = h /\ p_d v = d /\ p_data v <> 0 /\ p_cmap v = 0) c
       /\ rt_live RT Σ' = (p_data v, rsize v) :: (pix, 64) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (RASTER_COST + 8) <= rt_credit RT Σ').

End BiIface2.
