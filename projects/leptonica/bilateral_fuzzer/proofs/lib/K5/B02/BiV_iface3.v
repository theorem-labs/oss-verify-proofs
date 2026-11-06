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
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Km_setelem Km_iface Pm_iface Pm_iface2 Pm_iface4 Cf_iface RT_fk D_iface D_defs Bi_iface Bi_iface2 Bi_iface3 Bi_fktw BiV_defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section BiVIface3.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition pixBilateralExact_cps2V : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (cv : cmapv) (ks datas kr datar : Z) (rowss rowsr : list Z) (ras : list Z) (ksf rsf : Z -> Z -> Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 ks -> a2 = Z_to_bv 64 kr ->
  pix_obj (rt_live RT Σ) m pix v cv -> p_data v <> 0 ->
  kel_obj (rt_live RT Σ) m ks 41 41 20 20 datas rowss -> kel_obj (rt_live RT Σ) m kr 1 256 0 0 datar rowsr ->
  kel_vals m 41 rowss ksf -> ksf 20 20 = p_one_s -> kel_vals m 256 rowsr rsf -> rsf 0 0 = p_one_s ->
  uctx m sp s0 ras -> pbe_rows (bv_unsigned ra) ras ->
  lenv RT Σ m sp lo (LSTK 11) -> lres RT Σ 9 60 (PBE_COST2 - 2^21) ->
  sec_bytes (rt_live RT Σ) + PBE_SECB <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixBilateralExact m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix_obj (rt_live RT Σ') m' pix v cv /\ kel_obj (rt_live RT Σ') m' ks 41 41 20 20 datas rowss
          /\ kel_obj (rt_live RT Σ') m' kr 1 256 0 0 datar rowsr /\ kel_vals m' 41 rowss ksf /\ kel_vals m' 256 rowsr rsf
          /\ (pixd <> 0 -> pix_obj (rt_live RT Σ') m' pixd vd (mkCmapv 0 0 0 0) /\ p_cmap vd = 0 /\ p_data vd <> 0
                           /\ p_w vd = p_w v /\ p_h vd = p_h v /\ p_d vd = p_d v)) c
       /\ rt_live RT Σ' = (if pixd =? 0 then rt_live RT Σ else pix_new_live pixd vd (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (PBE_COST2 - 2^21) <= rt_credit RT Σ').

End BiVIface3.
