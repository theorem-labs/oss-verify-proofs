(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import Prelim SoftFloat FmtFp FmtFpDig FmtFpTail.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import FmtFpShapeC_u5.
Import ListNotations.
Import PML.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma nl_run_app : forall k a b, nl_run k (a ++ b) = match nl_run k a with Some k' => nl_run k' b | None => None end.
Proof.
  intros k a. revert k. induction a as [|c a IH]; intros k b; [reflexivity|].
  cbn [app nl_run]. destruct (nl_step k c); [apply IH | reflexivity].
Qed.

Lemma is_dig_of : forall c, isdig c -> is_dig c = true.
Proof. intros c H. unfold isdig in H. unfold is_dig. apply andb_true_iff. split; apply Z.leb_le; lia. Qed.

(* [comment removed for export] *)
Lemma nl_run_digits12 : forall t k, (k = 1 \/ k = 2) -> Forall isdig t -> exists k', nl_run k t = Some k' /\ (k' = 1 \/ k' = 2).
Proof.
  induction t as [|c t IH]; intros k Hk F; [exists k; split; [reflexivity| exact Hk]|].
  inversion F as [|? ? Hc Ft]; subst. pose proof (is_dig_of c Hc) as D. unfold isdig in Hc.
  cbn [nl_run]. unfold nl_step.
  destruct Hk as [-> | ->]; cbn [Z.eqb Pos.eqb].
  - replace (c =? 46) with false by (symmetry; apply Z.eqb_neq; lia).
    replace ((c =? 101) || (c =? 69))%bool with false by (symmetry; apply orb_false_iff; split; apply Z.eqb_neq; lia).
    rewrite D. apply IH; [right; reflexivity| exact Ft].
  - rewrite D. apply IH; [right; reflexivity| exact Ft].
Qed.

(* [comment removed for export] *)
Lemma nl_run_first_digit : forall c t k, (k = -1 \/ k = 0) -> isdig c -> Forall isdig t -> exists k', nl_run k (c :: t) = Some k' /\ (k' = 1 \/ k' = 2).
Proof.
  intros c t k Hk Hc Ft. pose proof (is_dig_of c Hc) as D. unfold isdig in Hc. cbn [nl_run]. unfold nl_step.
  destruct Hk as [-> | ->]; cbn [Z.eqb Pos.eqb].
  - replace (c =? 45) with false by (symmetry; apply Z.eqb_neq; lia).
    destruct (Z.eqb_spec c 48); [apply nl_run_digits12; [left; reflexivity| exact Ft]|].
    rewrite D. apply nl_run_digits12; [right; reflexivity| exact Ft].
  - destruct (Z.eqb_spec c 48); [apply nl_run_digits12; [left; reflexivity| exact Ft]|].
    rewrite D. apply nl_run_digits12; [right; reflexivity| exact Ft].
Qed.

(* [comment removed for export] *)
Lemma nl_run_frac_digits : forall t k, (k = 3 \/ k = 4) -> t <> [] -> Forall isdig t -> nl_run k t = Some 4.
Proof.
  induction t as [|c t IH]; intros k Hk NE F; [contradiction|].
  inversion F as [|? ? Hc Ft]; subst. pose proof (is_dig_of c Hc) as D. cbn [nl_run]. unfold nl_step.
  destruct Hk as [-> | ->]; cbn [Z.eqb Pos.eqb]; rewrite D;
    (destruct t as [|c2 t2]; [reflexivity| apply IH; [right; reflexivity| discriminate| exact Ft]]).
Qed.

(* [comment removed for export] *)
Lemma nl_run_exp_digits : forall t k, (k = 6 \/ k = 7) -> t <> [] -> Forall isdig t -> nl_run k t = Some 7.
Proof.
  induction t as [|c t IH]; intros k Hk NE F; [contradiction|].
  inversion F as [|? ? Hc Ft]; subst. pose proof (is_dig_of c Hc) as D. cbn [nl_run]. unfold nl_step.
  destruct Hk as [-> | ->]; cbn [Z.eqb Pos.eqb]; rewrite D;
    (destruct t as [|c2 t2]; [reflexivity| apply IH; [right; reflexivity| discriminate| exact Ft]]).
Qed.

(* [comment removed for export] *)
Lemma nl_run_frac : forall t2 k, (k = 1 \/ k = 2) -> frac_shape t2 -> exists k', nl_run k t2 = Some k' /\ (k' = 1 \/ k' = 2 \/ k' = 4).
Proof.
  intros t2 k Hk [-> | (t3 & -> & NE & F3)]; [exists k; split; [reflexivity| lia]|].
  cbn [nl_run]. unfold nl_step, CHR_dot. destruct Hk as [-> | ->]; cbn [Z.eqb Pos.eqb is_dig Z.leb Z.compare Pos.compare Pos.compare_cont andb].
  - exists 4. split; [apply nl_run_frac_digits; [left; reflexivity| exact NE| exact F3] | lia].
  - exists 4. split; [apply nl_run_frac_digits; [left; reflexivity| exact NE| exact F3] | lia].
Qed.

Lemma body_run : forall body k, (k = -1 \/ k = 0) -> f_body body \/ e_body body -> exists k', nl_run k body = Some k' /\ In k' [1; 2; 4; 7].
Proof.
  intros body k Hk [(t1 & t2 & -> & NE1 & F1 & FR) | (d & t2 & es & ed & -> & Dd & FR & Hes & NEd & Fd)].
  - destruct t1 as [|c t1]; [contradiction|]. inversion F1 as [|? ? Hc Ft1]; subst.
    pose proof (nl_run_app k (c :: t1) t2) as EA. cbn [app] in EA |- *. rewrite EA.
    destruct (nl_run_first_digit c t1 k Hk Hc Ft1) as [k1 (E1 & H1)]. rewrite E1.
    destruct (nl_run_frac t2 k1 H1 FR) as [k2 (E2 & H2)]. exists k2. split; [exact E2|]. cbn. lia.
  - pose proof (nl_run_app k (d :: t2) (101 :: es :: ed)) as EA. cbn [app] in EA |- *. rewrite EA.
    destruct (nl_run_first_digit d [] k Hk Dd (Forall_nil _)) as [k1 (E1 & H1)].
    pose proof (nl_run_app k [d] t2) as EB. cbn [app] in EB. rewrite EB, E1.
    destruct (nl_run_frac t2 k1 H1 FR) as [k2 (E2 & H2)]. rewrite E2.
    assert (E5 : nl_run k2 (101 :: es :: ed) = nl_run 6 ed).
    { cbn [nl_run]. unfold nl_step.
      destruct H2 as [-> | [-> | ->]]; cbn [Z.eqb Pos.eqb is_dig Z.leb Z.compare Pos.compare Pos.compare_cont andb orb];
        (destruct Hes as [-> | ->]; unfold CHR_plus, CHR_minus; cbn [Z.eqb Pos.eqb orb]; reflexivity). }
    rewrite E5. exists 7. split; [apply nl_run_exp_digits; [left; reflexivity| exact NEd| exact Fd]| cbn; tauto].
Qed.

Theorem gshape_num_final : forall t, gshape t -> num_final t.
Proof.
  intros t (sg & body & -> & [-> | ->] & B).
  - destruct (body_run body (-1) ltac:(left; reflexivity) B) as [k (E & H)]. exists k. split; [exact E| exact H].
  - cbn [app]. unfold num_final. cbn [nl_run]. unfold nl_step, CHR_minus. cbn [Z.eqb Pos.eqb].
    destruct (body_run body 0 ltac:(right; reflexivity) B) as [k (E & H)]. exists k. split; [exact E| exact H].
Qed.

(* [comment removed for export] *)
Theorem numf_proof : forall d prec o l, (prec = 15 \/ prec = 17) -> dfin d -> fmt_fp [] (f128_of_d d) 1 prec 0 CHR_g = Some (o, l) -> num_final o.
Proof. intros d prec o l Hp Hfin E. apply gshape_num_final. exact (fmt_fp_g_shape_of d prec o l Hp Hfin E). Qed.
