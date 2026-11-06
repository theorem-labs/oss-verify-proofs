(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Image.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import ImageA.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import Layout.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import RT_iface RT_traces RT_gaps_iface D_kit Lept_kit D_iface D_defs Lept_iface Gm_iface Gm_kit Gm_livekit LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma live_remove_ne : forall (l : list (Z * Z)) p e, In e (live_remove p l) -> fst e <> p.
Proof.
  intros l p e He. unfold live_remove in He. apply stdpp.base.list_elem_of_In in He.
  apply stdpp.list_basics.list.list_elem_of_filter in He. destruct He as (He & _).
  intros E. rewrite E, Z.eqb_refl in He. exact He.
Qed.
Lemma rm_opt_sub : forall (l : list (Z * Z)) p e, In e (rm_opt p l) -> In e l.
Proof. intros l p e He. unfold rm_opt in He. destruct (p =? 0); [exact He| exact (live_remove_sub l p e He)]. Qed.
Lemma rm_opt_ne : forall (l : list (Z * Z)) p e, p <> 0 -> In e (rm_opt p l) -> fst e <> p.
Proof. intros l p e NZ He. rewrite (rm_opt_nz p l NZ) in He. exact (live_remove_ne l p e He). Qed.

(* [comment removed for export] *)
Lemma live_destroy_In : forall (l : list (Z * Z)) pix v cv e, In e (live_destroy pix v cv l) ->
  In e l /\ fst e <> pix /\ (p_data v <> 0 -> fst e <> p_data v) /\ (p_cmap v <> 0 -> fst e <> p_cmap v /\ (c_arr cv <> 0 -> fst e <> c_arr cv)).
Proof.
  intros l pix v cv e He. unfold live_destroy in He.
  pose proof (live_remove_ne _ _ _ He) as N1. apply live_remove_sub in He.
  split; [exact (rm_opt_sub _ _ _ (rm_opt_sub _ _ _ (rm_opt_sub _ _ _ He)))|]. split; [exact N1|]. split.
  - intros NZ. apply (rm_opt_ne l (p_data v) e NZ). exact (rm_opt_sub _ _ _ (rm_opt_sub _ _ _ He)).
  - intros NZ. split; [exact (rm_opt_ne _ _ _ NZ He)|]. intros ANZ. apply rm_opt_sub in He.
    replace (p_cmap v =? 0) with false in He by (symmetry; apply Z.eqb_neq; exact NZ). exact (rm_opt_ne _ _ _ ANZ He).
Qed.

(* [comment removed for export] *)
Lemma pix_obj_agree_cm : forall (live : list (Z * Z)) (P : Z -> Prop) (m m' : mem) pix v cv,
  pix_obj live m pix v cv -> agree_on P m m' -> (p_cmap v <> 0 -> forall a, p_cmap v <= a < p_cmap v + 24 -> P a) ->
  rw_cells asegs m' pix (pix_cells v) -> pix_obj live m' pix v cv.
Proof.
  intros live P m m' pix v cv (PXC & PCH & HOK & PDATA & PCMAP) AG PL PXC'.
  split; [exact PXC'|]. split; [exact PCH|]. split; [exact HOK|]. split; [exact PDATA|].
  destruct PCMAP as [Z0|(CO & NN)]; [left; exact Z0| right]. split; [| exact NN].
  assert (NZ : p_cmap v <> 0) by (destruct CO as (_ & (_ & C0 & _) & _); lia).
  exact (cmap_obj_agree live P m m' (p_cmap v) cv CO AG (PL NZ)).
Qed.
