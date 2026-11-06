(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import Tac RzCPS.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface Lept_kit D_iface D_defs Lept_iface Gm_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma pix_obj_nocmap : forall (live live' : list (Z * Z)) (m m' : mem) pix v cv cv',
  pix_obj live m pix v cv -> p_cmap v = 0 -> (forall e, In e live -> In e live') ->
  rw_cells asegs m' pix (pix_cells v) -> pix_obj live' m' pix v cv'.
Proof.
  intros live live' m m' pix v cv cv' (_ & (CI & C0 & C16 & CN) & HOK & PD & _) NC SUB PXC.
  split; [exact PXC|]. split; [split; [exact (SUB _ CI)| tauto]|]. split; [exact HOK|]. split.
  - destruct PD as [Z0|((DI & D0 & D16 & DN) & DNE)]; [left; exact Z0| right]. split; [split; [exact (SUB _ DI)| tauto]| exact DNE].
  - left. exact NC.
Qed.

(* [comment removed for export] *)
Lemma pix_obj_nocmap_fields : forall (live live' : list (Z * Z)) (m m' : mem) pix v v' cv cv',
  pix_obj live m pix v cv -> p_cmap v = 0 -> (forall e, In e live -> In e live') ->
  p_w v' = p_w v -> p_h v' = p_h v -> p_d v' = p_d v -> p_wpl v' = p_wpl v -> p_data v' = p_data v -> p_cmap v' = 0 ->
  rw_cells asegs m' pix (pix_cells v') -> pix_obj live' m' pix v' cv'.
Proof.
  intros live live' m m' pix v v' cv cv' (_ & (CI & C0 & C16 & CN) & HOK & PD & _) NC SUB EW EH ED EWPL EDA ECM PXC.
  split; [exact PXC|]. split; [split; [exact (SUB _ CI)| tauto]|]. split.
  - unfold pix_hdr_ok in *. rewrite EW, EH, ED, EWPL. exact HOK.
  - split; [| left; exact ECM]. unfold rsize in *. rewrite EDA, EWPL, EH.
    destruct PD as [Z0|((DI & D0 & D16 & DN) & DNE)]; [left; exact Z0| right]. split; [split; [exact (SUB _ DI)| tauto]| exact DNE].
Qed.

Definition addborder_case (RT : rt_sig) (al : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs : Z) (vs : pixv) (cvs : cmapv) (val : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixs -> a1 = Z_to_bv 64 4 -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 2 -> a4 = Z_to_bv 64 8 -> a5 = Z_to_bv 64 val ->
  (val = 0 \/ val = 255) -> pix_obj (rt_live RT Σ) m pixs vs cvs -> p_d vs = 8 -> p_cmap vs = 0 -> p_data vs <> 0 ->
  lenv RT Σ m sp lo (LSTK 8) -> lres RT Σ 4 4 BORDER_COST -> bv_unsigned sp mod 32 = al ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixAddBorderGeneral m)))
    (fun c => exists (Σ' : rts RT) (r : Z) (v : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 r) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m' /\ new_pix8 RT Σ Σ' m' r (p_w vs + 12) (p_h vs + 10) v) c
       /\ new_pix8_live RT Σ Σ' r v
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - BORDER_COST <= rt_credit RT Σ').

Definition rmborder_case (RT : rt_sig) (al : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs : Z) (vs : pixv) (cvs : cmapv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixs -> a1 = Z_to_bv 64 4 -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 2 -> a4 = Z_to_bv 64 8 ->
  pix_obj (rt_live RT Σ) m pixs vs cvs -> p_d vs = 8 -> p_cmap vs = 0 -> p_data vs <> 0 -> 12 < p_w vs -> 10 < p_h vs ->
  lenv RT Σ m sp lo (LSTK 8) -> lres RT Σ 4 4 BORDER_COST -> bv_unsigned sp mod 32 = al ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixRemoveBorderGeneral m)))
    (fun c => exists (Σ' : rts RT) (r : Z) (v : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 r) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m' /\ new_pix8 RT Σ Σ' m' r (p_w vs - 12) (p_h vs - 10) v) c
       /\ new_pix8_live RT Σ Σ' r v
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - BORDER_COST <= rt_credit RT Σ').
