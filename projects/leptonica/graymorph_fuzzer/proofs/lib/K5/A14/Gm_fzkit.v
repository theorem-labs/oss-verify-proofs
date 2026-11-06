(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Image.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import ImageA.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import Layout.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import RT_iface RT_traces RT_gaps_iface D_kit Lept_kit D_iface D_defs Lept_iface Lept_objkit Gm_iface Gm_kit Gm_livekit Gm_livekit2 Gm_drvkit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma live_remove_app_fresh : forall p (pre l : list (Z * Z)), (forall e, In e pre -> fst e <> p) ->
  live_remove p (pre ++ l) = pre ++ live_remove p l.
Proof.
  intros p pre l. induction pre as [|[q k] pre IH]; intros F; [reflexivity|]. cbn [app].
  rewrite live_remove_other by (exact (F (q, k) (or_introl eq_refl))). f_equal. apply IH. intros e He. apply F. right. exact He.
Qed.
Lemma rm_opt_app_fresh : forall p (pre l : list (Z * Z)), (p <> 0 -> forall e, In e pre -> fst e <> p) ->
  rm_opt p (pre ++ l) = pre ++ rm_opt p l.
Proof.
  intros p pre l F. destruct (Z.eq_dec p 0) as [Z0|NZ]; [subst p; reflexivity|].
  rewrite !(rm_opt_nz p _ NZ). exact (live_remove_app_fresh p pre l (F NZ)).
Qed.
Lemma live_destroy_app_fresh : forall pix v cv (pre l : list (Z * Z)),
  (forall e, In e pre -> fst e <> pix /\ (p_data v <> 0 -> fst e <> p_data v) /\ (p_cmap v <> 0 -> fst e <> p_cmap v /\ fst e <> c_arr cv)) ->
  live_destroy pix v cv (pre ++ l) = pre ++ live_destroy pix v cv l.
Proof.
  intros pix v cv pre l F. unfold live_destroy.
  rewrite (rm_opt_app_fresh (p_data v) pre l) by (intros NZ e He; exact (proj1 (proj2 (F e He)) NZ)).
  rewrite (rm_opt_app_fresh (if p_cmap v =? 0 then 0 else c_arr cv) pre).
  2:{ intros NZ e He. destruct (Z.eq_dec (p_cmap v) 0) as [Z0|CNZ].
      - exfalso. apply NZ. rewrite Z0. reflexivity.
      - replace (p_cmap v =? 0) with false by (symmetry; apply Z.eqb_neq; exact CNZ). exact (proj2 (proj2 (proj2 (F e He)) CNZ)). }
  rewrite (rm_opt_app_fresh (p_cmap v) pre) by (intros NZ e He; exact (proj1 (proj2 (proj2 (F e He)) NZ))).
  apply live_remove_app_fresh. intros e He. exact (proj1 (F e He)).
Qed.

Lemma nodup_app_fresh : forall (pre l : list (Z * Z)), List.NoDup (map fst (pre ++ l)) ->
  forall e x, In e pre -> In x l -> fst e <> fst x.
Proof.
  intros pre l. induction pre as [|a pre IH]; intros ND e x He Hx; [destruct He|].
  cbn [app map] in ND. apply List.NoDup_cons_iff in ND. destruct ND as (NI & ND).
  destruct He as [<-|He]; [| exact (IH ND e x He Hx)].
  intros E. apply NI. rewrite E. rewrite List.map_app. apply List.in_or_app. right. apply List.in_map. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma pix_obj_entries : forall (live : list (Z * Z)) (m : mem) pix v cv, pix_obj live m pix v cv ->
  In (pix, 64) live /\ (p_data v <> 0 -> In (p_data v, rsize v) live)
  /\ (p_cmap v <> 0 -> In (p_cmap v, 24) live /\ In (c_arr cv, 4 * c_nalloc cv) live).
Proof.
  intros live m pix v cv (_ & (PIN & _) & _ & PD & PCM). split; [exact PIN|]. split.
  - intros NZ. destruct PD as [Z0|((DIN & _) & _)]; [exfalso; exact (NZ Z0)| exact DIN].
  - intros NZ. destruct PCM as [Z0|((_ & (CI & _) & (AI & _) & _) & _)]; [exfalso; exact (NZ Z0)|]. split; [exact CI| exact AI].
Qed.

(* [comment removed for export] *)
Lemma prefix_fresh_obj : forall (pre l : list (Z * Z)) (m : mem) pix v cv,
  List.NoDup (map fst (pre ++ l)) -> pix_obj l m pix v cv ->
  forall e, In e pre -> fst e <> pix /\ (p_data v <> 0 -> fst e <> p_data v) /\ (p_cmap v <> 0 -> fst e <> p_cmap v /\ fst e <> c_arr cv).
Proof.
  intros pre l m pix v cv ND PO e He. destruct (pix_obj_entries l m pix v cv PO) as (I1 & I2 & I3).
  split; [exact (nodup_app_fresh pre l ND e _ He I1)|]. split.
  - intros NZ. exact (nodup_app_fresh pre l ND e _ He (I2 NZ)).
  - intros NZ. destruct (I3 NZ) as (I4 & I5). split; [exact (nodup_app_fresh pre l ND e _ He I4)| exact (nodup_app_fresh pre l ND e _ He I5)].
Qed.
