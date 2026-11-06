(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA Arr FP.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Km_setelem Km_iface Pm_iface Pm_iface2 Pm_iface4 Cf_iface RT_fk Bi_iface Bi_iface2 D_iface D_defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition RA_BE_BGE : list Z := [0xd1078; 0xd1268; 0xd1294; 0xd12c0].
Definition RA_BE_DESTROY : list Z := [0xd1278; 0xd12a4; 0xd12d4; 0xd12f0; 0xd12f8; 0xd1300].
Definition RA_BBE_BE : Z := 0xd2144.
Definition bge_rows (r : Z) (ras : list Z) : Prop :=
  Forall (fun f => In (f :: RA_BGE_DESTROY :: r :: ras) CLIENT_TRACES) DESTROY_FREE_RAS
  /\ In (PMCOPY_CALLOC1 :: 0x9fdc0 :: 0xa028c :: RA_BGE_AMB :: r :: ras) CLIENT_TRACES.
Definition pbe_rows (ra : Z) (ras : list Z) : Prop :=
  Forall (fun r => bge_rows r (ra :: ras)) RA_BE_BGE
  /\ Forall (fun r => Forall (fun f => In (f :: r :: ra :: ras) CLIENT_TRACES) DESTROY_FREE_RAS) RA_BE_DESTROY.
Definition PBE_COST2 : Z := 14 * RASTER_COST + 2^22.

Section BiIface3.
Variable RT : rt_sig.

Definition pixBilateralExact_cps2 : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (cv : cmapv) (ks datas kr datar : Z) (rowss rowsr : list Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 ks -> a2 = Z_to_bv 64 kr ->
  pix_obj (rt_live RT Σ) m pix v cv -> p_data v <> 0 ->
  kel_obj (rt_live RT Σ) m ks 41 41 20 20 datas rowss -> kel_obj (rt_live RT Σ) m kr 1 256 0 0 datar rowsr ->
  uctx m sp s0 ras -> pbe_rows (bv_unsigned ra) ras ->
  lenv RT Σ m sp lo (LSTK 11) -> lres RT Σ 9 60 (PBE_COST2 - 2^21) ->
  sec_bytes (rt_live RT Σ) + PBE_SECB <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixBilateralExact m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix_obj (rt_live RT Σ') m' pix v cv /\ kel_obj (rt_live RT Σ') m' ks 41 41 20 20 datas rowss
          /\ kel_obj (rt_live RT Σ') m' kr 1 256 0 0 datar rowsr
          /\ (pixd <> 0 -> pix_obj (rt_live RT Σ') m' pixd vd (mkCmapv 0 0 0 0) /\ p_cmap vd = 0 /\ p_data vd <> 0
                           /\ p_w vd = p_w v /\ p_h vd = p_h v /\ p_d vd = p_d v)) c
       /\ rt_live RT Σ' = (if pixd =? 0 then rt_live RT Σ else pix_new_live pixd vd (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (PBE_COST2 - 2^21) <= rt_credit RT Σ').

Definition pixBlockBilateralExact_cps2 : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (cv : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> reg_get F r_fa0 = fs32 F_10_0 -> reg_get F r_fa1 = fs32 F_1_0 ->
  pix_obj (rt_live RT Σ) m pix v cv -> p_data v <> 0 ->
  uctx m sp s0 ras -> pbe_rows RA_BBE_BE (bv_unsigned ra :: ras) ->
  lenv RT Σ m sp lo (LSTK 12) -> lres RT Σ 10 (BI_FUZZ_LIVE - 16) PBE_COST2 ->
  sec_bytes (rt_live RT Σ) + PBE_SECB + 2^20 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixBlockBilateralExact m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix_obj (rt_live RT Σ') m' pix v cv
          /\ (pixd <> 0 -> pix_obj (rt_live RT Σ') m' pixd vd (mkCmapv 0 0 0 0) /\ p_cmap vd = 0 /\ p_data vd <> 0
                           /\ p_w vd = p_w v /\ p_h vd = p_h v /\ p_d vd = p_d v)) c
       /\ rt_live RT Σ' = (if pixd =? 0 then rt_live RT Σ else pix_new_live pixd vd (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - PBE_COST2 <= rt_credit RT Σ').

End BiIface3.
