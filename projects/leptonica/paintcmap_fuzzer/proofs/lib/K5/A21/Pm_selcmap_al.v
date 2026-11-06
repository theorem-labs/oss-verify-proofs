(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import ImageA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import Layout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Pm_iface D_iface D_defs.
Import ListNotations.
Open Scope Z_scope.

Section SELC_AL.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition pixSetSelectCmap_cps_al (k : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix b : Z) (v : pixv) (cv : cmapv),
  bv_unsigned sp mod 32 = k ->
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
Lemma pixSetSelectCmap_of_al : pixSetSelectCmap_cps_al 0 -> pixSetSelectCmap_cps_al 16 -> pixSetSelectCmap_cps RT.
Proof.
  intros H0 H16. unfold pixSetSelectCmap_cps.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix b v cv
    FDO MST ETP E0 E1 E2 E3 E4 E5 POBJ DNZ BOBJ BNE ENV RES.
  assert (SPA : bv_unsigned sp mod 16 = 0) by (unfold lenv in ENV; tauto).
  assert (AL : bv_unsigned sp mod 32 = 0 \/ bv_unsigned sp mod 32 = 16) by (clear - SPA; Z.div_mod_to_equations; lia).
  destruct AL as [AL|AL].
  - exact (H0 Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix b v cv
             AL FDO MST ETP E0 E1 E2 E3 E4 E5 POBJ DNZ BOBJ BNE ENV RES).
  - exact (H16 Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix b v cv
             AL FDO MST ETP E0 E1 E2 E3 E4 E5 POBJ DNZ BOBJ BNE ENV RES).
Qed.
End SELC_AL.
