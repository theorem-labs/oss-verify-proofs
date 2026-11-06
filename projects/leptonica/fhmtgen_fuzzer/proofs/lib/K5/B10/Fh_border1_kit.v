(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Image.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit D_iface D_defs Lept_iface Gm_iface Fh_iface LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma pix_obj_with_cmap : forall (live live' : list (Z * Z)) (m m' : mem) pix v v' cv cv',
  pix_obj live m pix v cv -> (forall e, In e live -> In e live') ->
  p_w v' = p_w v -> p_h v' = p_h v -> p_d v' = p_d v -> p_wpl v' = p_wpl v -> p_data v' = p_data v ->
  rw_cells asegs m' pix (pix_cells v') ->
  (p_cmap v' = 0 \/ (cmap_obj live' m' (p_cmap v') cv' /\ p_cmap v' <> pix /\ c_arr cv' <> pix /\ p_cmap v' <> p_data v' /\ c_arr cv' <> p_data v')) ->
  pix_obj live' m' pix v' cv'.
Proof.
  intros live live' m m' pix v v' cv cv' (_ & (CI & C0 & C16 & CN) & HOK & PD & _) SUB EW EH ED EWPL EDA PXC CM.
  split; [exact PXC|]. split; [split; [exact (SUB _ CI)| tauto]|]. split.
  - unfold pix_hdr_ok in *. rewrite EW, EH, ED, EWPL. exact HOK.
  - split; [| exact CM]. unfold rsize in *. rewrite EDA, EWPL, EH.
    destruct PD as [Z0|((DI & D0 & D16 & DN) & DNE)]; [left; exact Z0| right]. split; [split; [exact (SUB _ DI)| tauto]| exact DNE].
Qed.
