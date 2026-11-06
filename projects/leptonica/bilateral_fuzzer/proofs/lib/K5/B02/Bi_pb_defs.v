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
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Km_setelem Km_iface Pm_iface Pm_iface2 Pm_iface4 Cf_iface RT_fk Bi_iface D_iface D_defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition RA_PB_DESTROY : list Z := [0xce93c; 0xce970; 0xce9a8; 0xce9c4; 0xce9cc; 0xce9d4].
Definition pb_rows (ra : Z) (ras : list Z) : Prop :=
  Forall (fun r => Forall (fun f => In (f :: r :: ra :: ras) CLIENT_TRACES) DESTROY_FREE_RAS) RA_PB_DESTROY.

Section PbDefs.
Variable RT : rt_sig.
Definition pixBilateral_cps2 : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (cv : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 10 -> a2 = Z_to_bv 64 1 ->
  reg_get F r_fa0 = fs32 F_5_0 -> reg_get F r_fa1 = fs32 F_10_0 ->
  pix_obj (rt_live RT Σ) m pix v cv -> p_data v <> 0 ->
  uctx m sp s0 ras -> pb_rows (bv_unsigned ra) ras ->
  lenv RT Σ m sp lo (LSTK 12) -> lres RT Σ 11 (BI_FUZZ_LIVE - 16) PB_COST ->
  sec_bytes (rt_live RT Σ) + (PBG_SECB + 2^26 - 2^22) <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixBilateral m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m' /\ pix_obj (rt_live RT Σ') m' pix v cv
          /\ (pixd <> 0 -> pix_obj (rt_live RT Σ') m' pixd vd (mkCmapv 0 0 0 0) /\ p_cmap vd = 0 /\ p_data vd <> 0
                           /\ p_w vd = p_w v /\ p_h vd = p_h v /\ p_d vd = p_d v)) c
       /\ rt_live RT Σ' = (if pixd =? 0 then rt_live RT Σ else pix_new_live pixd vd (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - PB_COST <= rt_credit RT Σ').
End PbDefs.
