(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Image.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit D_iface D_defs.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Lept_iface.

Section IfaceNz.
Variable RT : rt_sig.

Definition pixDeserialize_nz_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (dp n : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 dp -> a1 = Z_to_bv 64 n -> 0 <= n < 2^26 -> 0 < dp -> (n < 28 \/ (dp mod 8 = 0 /\ own_live (rt_live RT Σ) dp n)) ->
  uctx m sp s0 ras ->
  Forall (fun r => Forall (fun f => In (f :: r :: bv_unsigned ra :: ras) CLIENT_TRACES) DESTROY_FREE_RAS) DESER_DESTROY_RAS ->
  lenv RT Σ m sp lo (LSTK 8) -> lres RT Σ 6 5 (RASTER_COST + 64) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixDeserialize m)))
    (fun c => exists (Σ' : rts RT) (pix : Z) (v : pixv) (cv : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pix) m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m' /\ (pix = 0 \/ (pix_obj (rt_live RT Σ') m' pix v cv /\ p_data v <> 0))) c
       /\ (pix = 0 -> rt_live RT Σ' = rt_live RT Σ)
       /\ (pix <> 0 -> live_destroy pix v cv (rt_live RT Σ') = rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (RASTER_COST + 64) <= rt_credit RT Σ'
       /\ (forall p n, In (p, n) (rt_live RT Σ') -> 0 < n) /\ Z.of_nat (length (rt_live RT Σ')) <= Z.of_nat (length (rt_live RT Σ)) + 4
       /\ (pix <> 0 -> p_cmap v <> 0 -> 1 <= c_n cv)).

Lemma pixDeserialize_cps_of_nz : pixDeserialize_nz_cps -> pixDeserialize_cps RT.
Proof.
  intros H. unfold pixDeserialize_cps.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo dp n ras P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12.
  eapply cps_conseq; [exact (H Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo dp n ras P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12)
                     | intros c Hc; exact Hc |].
  intros c (S' & pix & v & cv & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _).
  exists S', pix, v, cv. repeat (split; [assumption|]). assumption.
Qed.
End IfaceNz.
