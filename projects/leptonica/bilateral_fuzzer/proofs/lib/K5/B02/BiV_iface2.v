(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA Arr FP FpBound FpReal FpSiteB ExpfModelB ExpfTablesB.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Km_setelem Km_iface Pm_iface Pm_iface2 Pm_iface4 Cf_iface RT_fk D_iface D_defs Bi_iface Bi_iface2 Bi_fktw BiV_defs BiV_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section BiVIface2.
Variable RT : rt_sig.

Definition bilateralCreate_cps2V : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 10 -> a2 = Z_to_bv 64 1 ->
  reg_get F r_fa0 = fs32 F_5_0 -> reg_get F r_fa1 = fs32 F_10_0 ->
  pix8 (rt_live RT Σ) m pix v -> 22 <= p_w v -> 22 <= p_h v ->
  uctx m sp s0 ras -> Forall (fun f => In (f :: bv_unsigned ra :: ras) CLIENT_TRACES) BC_CALLOC_RAS ->
  (* [comment removed for export] *)
  In (PGLP_CALLOC :: RA_BC_LINEPTRS :: bv_unsigned ra :: ras) CLIENT_TRACES ->
  Forall (fun f => In (f :: RA_BC_DESTROY :: bv_unsigned ra :: ras) CLIENT_TRACES) DESTROY_FREE_RAS ->
  In (PMCOPY_CALLOC1 :: 0x9fdc0 :: 0xa028c :: RA_BC_AMB :: bv_unsigned ra :: ras) CLIENT_TRACES ->
  lenv RT Σ m sp lo (LSTK 10) -> lres RT Σ 9 48 BC_COST ->
  sec_bytes (rt_live RT Σ) + BC_SECB <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_bilateralCreate m)))
    (fun c => exists (Σ' : rts RT) (bil : Z) (b : bilv) (vsc : pixv) (ps : list pixe) (lps : list Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 bil) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [(pix + 20, pix + 24)] m m'
          /\ (bil = 0 -> pix8 (rt_live RT Σ') m' pix v)
          /\ (bil <> 0 -> b_pixs b = pix /\ bil_obj (rt_live RT Σ') m' bil b v vsc ps lps /\ exists kfs, kfr_vals m' (b_kfract b) kfs)) c
       /\ rt_live RT Σ' = (if bil =? 0 then rt_live RT Σ else bil_live bil b vsc ps lps (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - BC_COST <= rt_credit RT Σ').

Definition bilateralApply_cpsV : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (bil : Z) (b : bilv) (vs vsc : pixv) (ps : list pixe) (lps : list Z) (kfs : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 bil -> bil_obj (rt_live RT Σ) m bil b vs vsc ps lps -> kfr_vals m (b_kfract b) kfs ->
  lenv RT Σ m sp lo (LSTK 10) -> lres RT Σ 4 4 (RASTER_COST + 128) ->   (* [comment removed for export] *)
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_bilateralApply m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ bil_obj (rt_live RT Σ') m' bil b vs vsc ps lps
          /\ pixd <> 0 /\ pix8 (rt_live RT Σ') m' pixd vd /\ p_w vd = p_w vs /\ p_h vd = p_h vs) c
       /\ rt_live RT Σ' = pix_new_live pixd vd (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (RASTER_COST + 128) <= rt_credit RT Σ').

End BiVIface2.
