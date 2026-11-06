(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Image FP.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit D_iface D_defs D_libiface Lept_iface Gq_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section OpCase.
Variable RT : rt_sig.

Definition gq_op_case (al : Z) (entry ra_fuzz lvl frames chunks : Z) (cost : Z -> Z)
    (ARGS : word -> word -> word -> word -> word -> bvmap 5 word -> Prop) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (cv : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> ARGS a1 a2 a3 a4 a5 F ->
  pix_obj (rt_live RT Σ) m pix v cv -> p_data v <> 0 -> cmap_nz v cv ->
  uctx m sp s0 ras -> bv_unsigned ra = ra_fuzz -> ras = [RA_TOP] ->
  lenv RT Σ m sp lo (LSTK lvl) -> lres RT Σ frames chunks (cost (p_d v)) -> bv_unsigned sp mod 32 = al ->
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

Lemma gq_op_of_cases : forall entry ra_fuzz lvl frames chunks cost ARGS,
  gq_op_case 0 entry ra_fuzz lvl frames chunks cost ARGS -> gq_op_case 16 entry ra_fuzz lvl frames chunks cost ARGS ->
  gq_op_cps RT entry ra_fuzz lvl frames chunks cost ARGS.
Proof.
  intros entry ra_fuzz lvl frames chunks cost ARGS C0 C16.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix v cv ras
    H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 ENV H13.
  assert (AL : bv_unsigned sp mod 32 = 0 \/ bv_unsigned sp mod 32 = 16).
  { destruct ENV as (_ & _ & _ & _ & _ & _ & _ & _ & SPA & _). Z.div_mod_to_equations. lia. }
  destruct AL as [AL|AL].
  - exact (C0 Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix v cv ras
             H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 ENV H13 AL).
  - exact (C16 Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix v cv ras
             H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 ENV H13 AL).
Qed.
End OpCase.
