(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg NodesCfg LedgerCfg LazyCfg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import W64 ITrie FxState FxRel FxDrive FxDrive3 FxDrive3C.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import BackingAlgebra AsanPlanCore AsanPlan AsanPlanSound AsanNodesMmLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition is_cut (o : vop) : bool := match fst o with OpCut | OpCommit => true | _ => false end.
Definition is_lazyop (o : vop) : bool := match fst o with OpLazy => true | _ => false end.

Lemma ivs_wf_of_Forall l : Forall (fun q => e_hi q <= 2 ^ 64) l -> ivs_wf l.
Proof. intros H q Hq. exact (proj1 (Forall_forall _ _) H q Hq). Qed.

Lemma e_lo_le_hi p : e_lo p <= e_hi p.
Proof. unfold e_hi. pose proof (e_sz_nonneg p). lia. Qed.

Section Ops.
Variable rho : int -> word.

Lemma na_step_wf na o : ivs_wf na -> ivs_wf (na_step rho na o).
Proof.
  intros Hwf. unfold na_step. destruct (fst o); try exact Hwf; apply maps_subtract_wf; try exact Hwf; apply e_lo_le_hi.
Qed.

Lemma subtract_in l lo hi z : ivs_wf l -> lo <= hi ->
  APS.in_ivs z (maps_subtract l lo hi) = true -> APS.in_ivs z l = true.
Proof.
  intros Hwf Hlh H. rewrite in_ivs_covered in *.
  destruct (maps_subtract_sem l lo hi Hwf Hlh) as (_ & _ & Hcov). rewrite Hcov in H.
  apply andb_prop in H as [H _]. exact H.
Qed.

Lemma na_step_in na o z : ivs_wf na -> APS.in_ivs z (na_step rho na o) = true -> APS.in_ivs z na = true.
Proof.
  intros Hwf. unfold na_step. destruct (fst o); try (intros H; exact H); apply subtract_in; try exact Hwf; apply e_lo_le_hi.
Qed.

Lemma na_apply_in : forall ops na0 z, ivs_wf na0 ->
  APS.in_ivs z (na_apply rho ops na0) = true -> APS.in_ivs z na0 = true.
Proof.
  induction ops as [|o ops IH]; intros na0 z Hwf H; [exact H|].
  cbn [na_apply fold_left] in H. apply (na_step_in na0 o z Hwf).
  exact (IH _ z (na_step_wf na0 o Hwf) H).
Qed.

Lemma na_apply_keeps : forall ops na0 (q : word * word), In q na0 -> 0 < e_sz q ->
  (forall o, In o ops -> is_cut o = true ->
     e_lo (den rho (snd o)) < e_hi (den rho (snd o))
     /\ (e_hi q <= e_lo (den rho (snd o)) \/ e_hi (den rho (snd o)) <= e_lo q)) ->
  In q (na_apply rho ops na0).
Proof.
  induction ops as [|o ops IH]; intros na0 q Hq Hsz Hops; [exact Hq|].
  cbn [na_apply fold_left]. apply IH; [|exact Hsz | intros o' Ho'; apply Hops; right; exact Ho'].
  unfold na_step. pose proof (Hops o (or_introl eq_refl)) as Ho. unfold is_cut in Ho.
  destruct q as [b s]. unfold e_hi, e_lo, e_sz in *. cbn [fst snd] in *.
  destruct (fst o); try exact Hq; destruct (Ho eq_refl) as [Hlt Hd]; apply maps_subtract_keeps; try assumption; lia.
Qed.

(* [comment removed for export] *)
Lemma subtract_keeps_pt l lo hi z : ivs_wf l -> lo <= hi -> APS.in_ivs z l = true -> ~ (lo <= z < hi) ->
  APS.in_ivs z (maps_subtract l lo hi) = true.
Proof.
  intros Hwf Hlh Hin Hout. rewrite in_ivs_covered in *.
  destruct (maps_subtract_sem l lo hi Hwf Hlh) as (_ & _ & Hcov). rewrite Hcov, Hin. cbn [andb].
  apply negb_true_iff. unfold in_rng. apply andb_false_iff.
  destruct (Z_lt_dec z lo); [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
Qed.

Lemma na_apply_keeps_pt : forall ops na0 z, ivs_wf na0 -> APS.in_ivs z na0 = true ->
  (forall o, In o ops -> is_cut o = true -> ~ (e_lo (den rho (snd o)) <= z < e_hi (den rho (snd o)))) ->
  APS.in_ivs z (na_apply rho ops na0) = true.
Proof.
  induction ops as [|o ops IH]; intros na0 z Hwf Hin Hops; [exact Hin|].
  cbn [na_apply fold_left]. apply IH; [exact (na_step_wf na0 o Hwf) | | intros o' Ho'; apply Hops; right; exact Ho'].
  unfold na_step. pose proof (Hops o (or_introl eq_refl)) as Ho. unfold is_cut in Ho.
  destruct (fst o); try exact Hin; apply subtract_keeps_pt; try assumption; try apply e_lo_le_hi; exact (Ho eq_refl).
Qed.

(* [comment removed for export] *)
Lemma subtract_page (p : word) l lo hi : ivs_wf l ->
  page_in_ranges p (maps_subtract l lo hi) = true -> page_in_ranges p l = true.
Proof.
  intros Hwf H. unfold page_in_ranges in *. apply existsb_exists in H as (q & Hq & Hpq). cbv zeta in Hpq.
  destruct (maps_subtract_pieces l lo hi q Hwf Hq) as (r & Hr & H1 & H2 & _).
  apply existsb_exists. exists r. split; [exact Hr|]. cbv zeta.
  apply andb_prop in Hpq as [P1 P2]. apply Z.leb_le in P1, P2. apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

Lemma lz_step_wf lz o : ivs_wf lz -> (is_lazyop o = true -> e_hi (den rho (snd o)) <= 2 ^ 64) -> ivs_wf (lz_step rho lz o).
Proof.
  intros Hwf Ho. unfold lz_step. unfold is_lazyop in Ho.
  destruct (fst o); try exact Hwf; try (apply maps_subtract_wf; try exact Hwf; apply e_lo_le_hi).
  apply ivs_wf_cons; [|exact Hwf]. exact (Ho eq_refl).
Qed.

Lemma lz_step_page lz o (p : word) : ivs_wf lz ->
  page_in_ranges p (lz_step rho lz o) = true ->
  page_in_ranges p lz = true
  \/ (is_lazyop o = true /\ e_lo (den rho (snd o)) <= bv_unsigned p /\ bv_unsigned p + page_size <= e_hi (den rho (snd o))).
Proof.
  intros Hwf. unfold lz_step, is_lazyop. destruct (fst o); try (intros H; left; exact H);
    try (intros H; left; exact (subtract_page p lz _ _ Hwf H)).
  rewrite page_in_ranges_cons. intros H. apply orb_prop in H as [H|H]; [right | left; exact H].
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. unfold e_hi, e_lo, e_sz. split; [reflexivity|]. lia.
Qed.

Lemma lz_apply_page : forall ops lz0 (p : word), ivs_wf lz0 ->
  (forall o, In o ops -> is_lazyop o = true -> e_hi (den rho (snd o)) <= 2 ^ 64) ->
  page_in_ranges p (lz_apply rho ops lz0) = true ->
  page_in_ranges p lz0 = true
  \/ exists o, In o ops /\ is_lazyop o = true
               /\ e_lo (den rho (snd o)) <= bv_unsigned p /\ bv_unsigned p + page_size <= e_hi (den rho (snd o)).
Proof.
  induction ops as [|o ops IH]; intros lz0 p Hwf Hops H; [left; exact H|].
  cbn [lz_apply fold_left] in H.
  destruct (IH _ p (lz_step_wf lz0 o Hwf (Hops o (or_introl eq_refl))) (fun o' Ho' => Hops o' (or_intror Ho')) H)
    as [H1 | (o' & Ho' & H2)].
  - destruct (lz_step_page lz0 o p Hwf H1) as [H3|H3]; [left; exact H3 | right; exists o; split; [left; reflexivity | exact H3]].
  - right. exists o'. split; [right; exact Ho' | exact H2].
Qed.

Lemma lz_apply_forall (P : word * word -> Prop) :
  (forall q r : word * word, P r -> e_lo r <= e_lo q -> e_hi q <= e_hi r -> P q) ->
  forall ops lz0, ivs_wf lz0 -> Forall P lz0 ->
  (forall o, In o ops -> is_lazyop o = true -> P (den rho (snd o)) /\ e_hi (den rho (snd o)) <= 2 ^ 64) ->
  Forall P (lz_apply rho ops lz0).
Proof.
  intros Hsub. induction ops as [|o ops IH]; intros lz0 Hwf HP Hops; [exact HP|].
  cbn [lz_apply fold_left].
  apply IH; [exact (lz_step_wf lz0 o Hwf (fun Hl => proj2 (Hops o (or_introl eq_refl) Hl))) | | intros o' Ho'; apply Hops; right; exact Ho'].
  unfold lz_step. pose proof (Hops o (or_introl eq_refl)) as Ho. unfold is_lazyop in Ho.
  assert (Hcut : Forall P (maps_subtract lz0 (e_lo (den rho (snd o))) (e_hi (den rho (snd o))))).
  { apply Forall_forall. intros q Hq. destruct (maps_subtract_pieces lz0 _ _ q Hwf Hq) as (r & Hr & H1 & H2 & _).
    apply (Hsub q r (proj1 (Forall_forall _ _) HP r Hr)); unfold e_hi, e_lo, e_sz; lia. }
  destruct (fst o); try exact HP; try exact Hcut.
  constructor; [exact (proj1 (Ho eq_refl)) | exact HP].
Qed.

(* [comment removed for export] *)
Lemma subtract_out_pt l lo hi z : ivs_wf l -> lo <= hi -> lo <= z < hi -> APS.in_ivs z (maps_subtract l lo hi) = false.
Proof.
  intros Hwf Hlh Hz. rewrite in_ivs_covered.
  destruct (maps_subtract_sem l lo hi Hwf Hlh) as (_ & _ & Hcov). rewrite Hcov.
  apply andb_false_iff. right. apply negb_false_iff. unfold in_rng. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma na_apply_cut_pt : forall ops na0 o z, ivs_wf na0 -> In o ops -> is_cut o = true ->
  e_lo (den rho (snd o)) <= z < e_hi (den rho (snd o)) -> APS.in_ivs z (na_apply rho ops na0) = false.
Proof.
  induction ops as [|o1 ops IH]; intros na0 o z Hwf Hin Hcut Hz; [destruct Hin|].
  cbn [na_apply fold_left]. destruct Hin as [->|Hin].
  - apply not_true_is_false. intros H. pose proof (na_apply_in ops _ z (na_step_wf na0 o Hwf) H) as H1.
    unfold na_step in H1. unfold is_cut in Hcut.
    destruct (fst o); try discriminate; rewrite (subtract_out_pt na0 _ _ z Hwf (e_lo_le_hi _) Hz) in H1; discriminate.
  - exact (IH _ o z (na_step_wf na0 o1 Hwf) Hin Hcut Hz).
Qed.

Lemma lz_apply_cut_page : forall ops lz0 o (p : word), ivs_wf lz0 ->
  (forall o', In o' ops -> is_lazyop o' = true -> e_hi (den rho (snd o')) <= 2 ^ 64) ->
  In o ops -> is_cut o = true -> e_hi (den rho (snd o)) < 2 ^ 64 ->
  e_lo (den rho (snd o)) <= bv_unsigned p -> bv_unsigned p + page_size <= e_hi (den rho (snd o)) ->
  (forall o2, In o2 ops -> is_lazyop o2 = true ->
     ~ (e_lo (den rho (snd o2)) <= bv_unsigned p /\ bv_unsigned p + page_size <= e_hi (den rho (snd o2)))) ->
  page_in_ranges p (lz_apply rho ops lz0) = false.
Proof.
  induction ops as [|o1 ops IH]; intros lz0 o p Hwf Hops Hin Hcut Hhi Hlo Hpe Hnl; [destruct Hin|].
  cbn [lz_apply fold_left]. destruct Hin as [->|Hin].
  - apply not_true_is_false. intros H.
    destruct (lz_apply_page ops _ p (lz_step_wf lz0 o Hwf (Hops o (or_introl eq_refl))) (fun o' Ho' => Hops o' (or_intror Ho')) H)
      as [H1 | (o2 & Ho2 & Hl2 & H2)].
    + unfold lz_step in H1. unfold is_cut in Hcut. unfold page_size in *.
      destruct (fst o); try discriminate;
        destruct (FxDrive3C.page_in_ranges_subtract_out p lz0 _ _ (e_lo_le_hi _) Hhi H1) as [Hq|Hq]; lia.
    + exact (Hnl o2 (or_intror Ho2) Hl2 H2).
  - apply (IH _ o p (lz_step_wf lz0 o1 Hwf (Hops o1 (or_introl eq_refl))) (fun o' Ho' => Hops o' (or_intror Ho')) Hin Hcut Hhi Hlo Hpe).
    intros o2 Ho2. exact (Hnl o2 (or_intror Ho2)).
Qed.

End Ops.
