(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface D_kit Lept_kit D_iface D_defs Lept_iface Lept_objkit
  Gm_iface Gq_iface Gm_kit Gm_livekit Gm_livekit2 Gm_drvkit Gm_drvkit2 Gm_fzkit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition okeys (p : Z) : list Z := if p =? 0 then [] else [p].
Lemma rm_opt_fold : forall p (l : list (Z * Z)), rm_opt p l = fold_right live_remove l (okeys p).
Proof. intros p l. unfold rm_opt, okeys. destruct (p =? 0); reflexivity. Qed.
Definition dks (pix : Z) (v : pixv) (cv : cmapv) : list Z :=
  pix :: okeys (p_cmap v) ++ okeys (if p_cmap v =? 0 then 0 else c_arr cv) ++ okeys (p_data v).
Lemma live_destroy_fold : forall pix v cv (l : list (Z * Z)), live_destroy pix v cv l = fold_right live_remove l (dks pix v cv).
Proof.
  intros. unfold live_destroy, dks. rewrite !rm_opt_fold. cbn [fold_right]. rewrite !List.fold_right_app. reflexivity.
Qed.
Lemma fold_remove_comm1 : forall q ks (l : list (Z * Z)),
  live_remove q (fold_right live_remove l ks) = fold_right live_remove (live_remove q l) ks.
Proof.
  intros q ks. induction ks as [|k ks IH]; intros l; [reflexivity|]. cbn [fold_right]. rewrite live_remove_comm. rewrite IH. reflexivity.
Qed.
Lemma fold_remove_swap : forall ks1 ks2 (l : list (Z * Z)),
  fold_right live_remove (fold_right live_remove l ks2) ks1 = fold_right live_remove (fold_right live_remove l ks1) ks2.
Proof.
  intros ks1. induction ks1 as [|k ks1 IH]; intros ks2 l; [reflexivity|]. cbn [fold_right]. rewrite IH. apply fold_remove_comm1.
Qed.
Lemma live_destroy_comm : forall p1 v1 c1 p2 v2 c2 (l : list (Z * Z)),
  live_destroy p1 v1 c1 (live_destroy p2 v2 c2 l) = live_destroy p2 v2 c2 (live_destroy p1 v1 c1 l).
Proof. intros. rewrite !live_destroy_fold. apply fold_remove_swap. Qed.

(* [comment removed for export] *)
Lemma rm_opt_keep : forall (l : list (Z * Z)) p e, In e l -> (p <> 0 -> fst e <> p) -> In e (rm_opt p l).
Proof.
  intros l p e He NE. unfold rm_opt. destruct (Z.eqb_spec p 0) as [Z0|NZ]; [exact He|].
  apply live_remove_keep; [exact He| exact (NE NZ)].
Qed.
Lemma live_destroy_keep : forall (l : list (Z * Z)) pix v cv e, In e l ->
  fst e <> pix -> (p_data v <> 0 -> fst e <> p_data v) -> (p_cmap v <> 0 -> fst e <> p_cmap v /\ (c_arr cv <> 0 -> fst e <> c_arr cv)) ->
  In e (live_destroy pix v cv l).
Proof.
  intros l pix v cv e He N1 N2 N3. unfold live_destroy.
  apply live_remove_keep; [| exact N1].
  apply rm_opt_keep; [| intros NZ; exact (proj1 (N3 NZ))].
  apply rm_opt_keep; [| destruct (Z.eqb_spec (p_cmap v) 0) as [Z0|NZ]; [intros X; exfalso; exact (X eq_refl)| intros AZ; exact (proj2 (N3 NZ) AZ)]].
  apply rm_opt_keep; [exact He| exact N2].
Qed.

(* [comment removed for export] *)
Lemma pix_obj_pos : forall (live : list (Z * Z)) (m : mem) pix v cv, pix_obj live m pix v cv ->
  0 < pix /\ (p_data v <> 0 -> 0 < p_data v) /\ (p_cmap v <> 0 -> 0 < p_cmap v /\ 0 < c_arr cv).
Proof.
  intros live m pix v cv (_ & (_ & P0 & _) & _ & PD & PCM). split; [exact P0|]. split.
  - intros NZ. destruct PD as [Z0|((_ & D0 & _) & _)]; [exfalso; exact (NZ Z0)| exact D0].
  - intros NZ. destruct PCM as [Z0|((_ & (_ & C0 & _) & (_ & A0 & _) & _) & _)]; [exfalso; exact (NZ Z0)|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition obj_fresh (r : Z) (vr : pixv) (cvr : cmapv) (p : Z) (v : pixv) (cv : cmapv) : Prop :=
  forall k, In k ([r] ++ (if p_data vr =? 0 then [] else [p_data vr]) ++ (if p_cmap vr =? 0 then [] else [p_cmap vr; c_arr cvr])) ->
  k <> p /\ (p_data v <> 0 -> k <> p_data v) /\ (p_cmap v <> 0 -> k <> p_cmap v /\ k <> c_arr cv).
Lemma pix_obj_in_destroy : forall (L : list (Z * Z)) (m : mem) r vr cvr p v cv,
  pix_obj L m r vr cvr -> obj_fresh r vr cvr p v cv -> pix_obj (live_destroy p v cv L) m r vr cvr.
Proof.
  intros L m r vr cvr p v cv PO FR.
  assert (KEEP : forall e, In e L -> In (fst e) ([r] ++ (if p_data vr =? 0 then [] else [p_data vr]) ++ (if p_cmap vr =? 0 then [] else [p_cmap vr; c_arr cvr])) ->
                 In e (live_destroy p v cv L)).
  { intros e He Hk. destruct (FR _ Hk) as (N1 & N2 & N3).
    apply live_destroy_keep; [exact He| exact N1| exact N2|]. intros NZ. destruct (N3 NZ) as (Q1 & Q2). split; [exact Q1| intros _; exact Q2]. }
  destruct PO as (PXC & (PIN & P0 & P16 & PN) & HOK & PD & PCM).
  split; [exact PXC|]. split; [split; [apply (KEEP _ PIN); cbn [fst]; left; reflexivity| repeat split; assumption]|]. split; [exact HOK|]. split.
  - destruct PD as [Z0|((DIN & D0 & D16 & DN) & DNE)]; [left; exact Z0| right]. split; [| exact DNE].
    split; [| repeat split; assumption]. apply (KEEP _ DIN). cbn [fst]. apply in_or_app. right. apply in_or_app. left.
    replace (p_data vr =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity.
  - destruct PCM as [Z0|(CO & R)]; [left; exact Z0| right]. split; [| exact R].
    destruct CO as (CC & (CIN & C0 & C16 & CN) & (AIN & A0 & A16 & AN) & COK & CNE).
    assert (NZ : (p_cmap vr =? 0) = false) by (apply Z.eqb_neq; lia).
    split; [exact CC|]. split; [split; [| repeat split; assumption]|].
    + apply (KEEP _ CIN). cbn [fst]. apply in_or_app. right. apply in_or_app. right. rewrite NZ. left. reflexivity.
    + split; [split; [| repeat split; assumption]| split; assumption].
      apply (KEEP _ AIN). cbn [fst]. apply in_or_app. right. apply in_or_app. right. rewrite NZ. right. left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma obj_fresh_of_eq : forall (Ld Lc : list (Z * Z)) (md : mem) r vr cvr (m : mem) p v cv,
  live_destroy r vr cvr Ld = Lc -> pix_obj Ld md r vr cvr -> pix_obj Lc m p v cv -> obj_fresh r vr cvr p v cv.
Proof.
  intros Ld Lc md r vr cvr m p v cv EQ POR POP k Hk.
  destruct (pix_obj_entries Lc m p v cv POP) as (I1 & I2 & I3).
  destruct (pix_obj_pos Ld md r vr cvr POR) as (R0 & RD & RC).
  assert (NE : forall e, In e Lc -> fst e <> k).
  { intros e He. rewrite <- EQ in He. destruct (live_destroy_In _ _ _ _ _ He) as (_ & N1 & N2 & N3).
    cbn [app In] in Hk. destruct Hk as [<-|Hk]; [exact N1|].
    apply in_app_or in Hk. destruct Hk as [Hk|Hk].
    - destruct (Z.eqb_spec (p_data vr) 0) as [Z0|NZ]; [destruct Hk|]. cbn [In] in Hk. destruct Hk as [<-|[]]. exact (N2 NZ).
    - destruct (Z.eqb_spec (p_cmap vr) 0) as [Z0|NZ]; [destruct Hk|]. cbn [In] in Hk. destruct (N3 NZ) as (Q1 & Q2).
      destruct Hk as [<-|[<-|[]]]; [exact Q1|]. apply Q2. destruct (RC NZ) as (_ & A0). lia. }
  split; [intros E; exact (NE _ I1 (eq_sym E))|]. split.
  - intros NZ E. exact (NE _ (I2 NZ) (eq_sym E)).
  - intros NZ. destruct (I3 NZ) as (I4 & I5). split; intros E; [exact (NE _ I4 (eq_sym E))| exact (NE _ I5 (eq_sym E))].
Qed.

(* [comment removed for export] *)
Lemma agree_fp_sub : forall (live : list (Z * Z)) frs sp W W' (m m' : mem),
  agree_on (fun a => aclient live frs sp a /\ outside W a) m m' ->
  (forall x, outside W' x -> outside W x) ->
  agree_on (fun a => aclient live frs sp a /\ outside W' a) m m'.
Proof. intros live frs sp W W' m m' AG SUB a (Ha & Ho). apply AG. split; [exact Ha| exact (SUB _ Ho)]. Qed.

(* [comment removed for export] *)
Lemma gq_costs_ok : forall d,
  0 < D2_COST d /\ 0 < DBIN_COST d /\ 0 < BAND_COST d /\ 0 < BAND32_COST d /\ 0 < DISCR32_COST d /\ 0 < THR_COST d
  /\ (RASTER_COST + 65) + 6 * (TEMPLATE_COST + 2) + (D2_COST d + DBIN_COST d + BAND_COST d + BAND32_COST d + DISCR32_COST d + THR_COST d) + 16 <= 2^31.
Proof.
  intros d. unfold D2_COST, DBIN_COST, BAND_COST, BAND32_COST, DISCR32_COST, THR_COST, OP_COST, is_d8, is_d32, is_d248, TEMPLATE_COST, MSG_COST, RASTER_COST.
  destruct (Z.eqb_spec d 8) as [-> | N8]; [cbn; lia|].
  destruct (Z.eqb_spec d 32) as [-> | N32]; [cbn; lia|].
  destruct (d =? 2); destruct (d =? 4); cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma live_remove_len' : forall (l : list (Z * Z)) p, (length (live_remove p l) <= length l)%nat.
Proof. intros l p. unfold live_remove. apply stdpp.list_basics.list.length_filter. Qed.
Lemma rm_opt_len : forall (l : list (Z * Z)) p, (length (rm_opt p l) <= length l)%nat.
Proof. intros l p. unfold rm_opt. destruct (p =? 0); [lia| apply live_remove_len']. Qed.
Lemma live_destroy_len : forall pix v cv (l : list (Z * Z)), (length (live_destroy pix v cv l) <= length l)%nat.
Proof.
  intros. unfold live_destroy.
  set (a := if p_cmap v =? 0 then 0 else c_arr cv).
  pose proof (rm_opt_len l (p_data v)) as H1.
  pose proof (rm_opt_len (rm_opt (p_data v) l) a) as H2.
  pose proof (rm_opt_len (rm_opt a (rm_opt (p_data v) l)) (p_cmap v)) as H3.
  pose proof (live_remove_len' (rm_opt (p_cmap v) (rm_opt a (rm_opt (p_data v) l))) pix) as H4.
  lia.
Qed.
Lemma live_destroy_sub : forall pix v cv (l : list (Z * Z)) e, In e (live_destroy pix v cv l) -> In e l.
Proof. intros pix v cv l e He. exact (proj1 (live_destroy_In _ _ _ _ _ He)). Qed.

Section FzKit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

(* [comment removed for export] *)
Lemma keeps_live_others : forall Σ (m0 : mem) frs sp (L : list (Z * Z)) p n lo hi (m m' : mem),
  ART RT Σ m0 -> In (p, n) (rt_live RT Σ) -> p <= lo -> hi <= p + n ->
  (forall e, In e L -> In e (rt_live RT Σ) /\ fst e <> p) ->
  agree_on (fun a => aclient (rt_live RT Σ) frs sp a /\ outside [(lo, hi)] a) m m' ->
  keeps_live L m m'.
Proof using AF.
  intros Σ m0 frs sp L p n lo hi m m' HA HP LO HI SUB AG b k Hin a Ha. apply AG.
  destruct (SUB _ Hin) as (Hl & NE). cbn [fst] in NE.
  split; [right; right; left; exists b, k; split; [exact Hl| exact Ha]|].
  pose proof (live_apart2 RT AF Σ m0 b k p n HA Hl HP ltac:(intros E; inversion E; exact (NE ltac:(assumption)))) as D.
  cbn [outside]. split; [lia| exact I].
Qed.
End FzKit.

(* [comment removed for export] *)
Lemma live_destroy_mono : forall pix v cv (L L' : list (Z * Z)), (forall e, In e L -> In e L') ->
  forall e, In e (live_destroy pix v cv L) -> In e (live_destroy pix v cv L').
Proof.
  intros pix v cv L L' SUB e He. destruct (live_destroy_In _ _ _ _ _ He) as (I1 & N1 & N2 & N3).
  exact (live_destroy_keep L' pix v cv e (SUB _ I1) N1 N2 N3).
Qed.
