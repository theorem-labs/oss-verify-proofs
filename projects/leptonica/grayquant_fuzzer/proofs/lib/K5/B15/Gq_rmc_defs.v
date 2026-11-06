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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit D_iface D_defs Lept_iface Gm_iface Gq_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section RMC_DEFS.
Variable RT : rt_sig.

Definition pixRemoveColormap_case (al : Z) (cm : bool) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (cv : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 1 ->
  pix_obj (rt_live RT Σ) m pix v cv -> p_d v = 8 -> p_data v <> 0 -> cmap_nz v cv ->
  uctx m sp s0 ras ->
  (p_cmap v <> 0 -> Forall (fun f => In (f :: bv_unsigned ra :: ras) CLIENT_TRACES \/ In [f] CLIENT_TRACES) REMOVE_RAS) ->
  lenv RT Σ m sp lo (LSTK 8) -> lres RT Σ 4 7 REMOVE_COST ->
  bv_unsigned sp mod 32 = al -> (if cm then p_cmap v <> 0 else p_cmap v = 0) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixRemoveColormap m)))
    (fun c => exists (Σ' : rts RT) (r : Z) (vr : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 r) m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo
          /\ keepsL RT (rt_live RT Σ) Σ sp [(pix + 20, pix + 24)] m m'
          /\ ((p_cmap v = 0 /\ r = pix /\ pix_obj_rc (rt_live RT Σ') m' pix v cv 2)
              \/ (p_cmap v <> 0 /\ pix_obj (rt_live RT Σ') m' pix v cv
                  /\ pix_obj (rt_live RT Σ') m' r vr (mkCmapv 0 0 0 0)
                  /\ p_w vr = p_w v /\ p_h vr = p_h v /\ p_d vr = 8 /\ p_data vr <> 0 /\ p_cmap vr = 0))) c
       /\ (p_cmap v = 0 -> rt_live RT Σ' = rt_live RT Σ)
       /\ (p_cmap v <> 0 -> rt_live RT Σ' = (p_data vr, rsize vr) :: (r, 64) :: rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - REMOVE_COST <= rt_credit RT Σ').

Lemma pixRemoveColormap_of_cases :
  pixRemoveColormap_case 0 false -> pixRemoveColormap_case 16 false ->
  pixRemoveColormap_case 0 true -> pixRemoveColormap_case 16 true -> pixRemoveColormap_gray_cps RT.
Proof.
  intros N0 N16 Y0 Y16. unfold pixRemoveColormap_gray_cps.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix v cv ras
    FDO MST TP A0 A1 POBJ D8 VDATA NZV UC TRS ENV RES.
  assert (AL : bv_unsigned sp mod 32 = 0 \/ bv_unsigned sp mod 32 = 16).
  { destruct ENV as (_ & _ & _ & _ & _ & _ & _ & _ & SPA & _). Z.div_mod_to_equations; lia. }
  destruct (Z.eq_dec (p_cmap v) 0) as [CZ|CNZ]; destruct AL as [AL|AL];
    [ eapply (N0 Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1) | eapply (N16 Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1)
    | eapply (Y0 Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1) | eapply (Y16 Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1) ]; eassumption.
Qed.
End RMC_DEFS.
