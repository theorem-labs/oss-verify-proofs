(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Lib Require Import ITree Nodes CTree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Spec Require Import Prelim Monad MSafe MSafeP StepB LB_Logic CMonad.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.


Lemma twf_hmap : forall {R R'} (g : R -> hist -> R') (t : itree node R) h mo (P' : R' -> Model -> Prop),
  twf t mo (fun r mo1 => forall h', P' (g r h') mo1) -> twf (hmap g t h) mo P'.
Proof.
  intros R R' g t. induction t as [r|n k IH]; intros h mo P' H; cbn in *.
  - apply H.
  - destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. apply IH. eapply Hk; eauto.
Qed.

Lemma twfP_hmap : forall {R R'} (g : R -> hist -> R') (t : itree node R) h mo (P' : R' -> Model -> Prop),
  twfP t mo (fun r mo1 => forall h', P' (g r h') mo1) -> twfP (hmap g t h) mo P'.
Proof.
  intros R R' g t. induction t as [r|n k IH]; intros h mo P' H; cbn in *.
  - apply H.
  - destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. apply IH. eapply Hk; eauto.
Qed.

Lemma twl_hmap : forall {R R'} B (g : R -> hist -> R') (t : itree node R) h mo (P' : R' -> Model -> Prop),
  twl B t mo (fun r mo1 => forall h', P' (g r h') mo1) -> twl B (hmap g t h) mo P'.
Proof.
  intros R R' B g t. induction t as [r|n k IH]; intros h mo P' H; cbn -[NF] in *.
  - apply H.
  - destruct H as [HN Hk]. split; [exact HN|]. intros rsp mo' evs Hst.
    destruct (Hk rsp mo' evs Hst) as [HB Hk']. split; [exact HB|]. apply IH. exact Hk'.
Qed.

Section CSpec.
Context {St : Type}.
Local Notation assn := (assn St).

Lemma mspec_mtag {A} (P : assn) (m : M St A) (Q : A -> assn) h :
  mspec P m Q -> mspec P (mtag m h) (fun ah => Q (fst ah)).
Proof.
  intros H s mo HP. unfold mtag, etwf. apply twf_hmap. eapply twf_mono; [exact (H s mo HP)|].
  intros [|[a s1]] mo1 H1 h'; cbn in *; exact H1.
Qed.

Definition cspec {A} (P : assn) (mc : MC St A) (Q : A -> assn) : Prop :=
  forall D h, mspec P (RESX D h mc) (fun ah => Q (fst ah)).

Lemma cspec_lift {A} (P : assn) (m : M St A) (Q : A -> assn) : mspec P m Q -> cspec P (clift m) Q.
Proof. intros H D h. rewrite RESX_lift. apply mspec_mtag. exact H. Qed.

Lemma cspec_ret {A} (a : A) (P : assn) (Q : A -> assn) : (forall s mo, P s mo -> Q a s mo) -> cspec P (cmret a) Q.
Proof. intros H D h. rewrite RESX_ret. apply mspec_ret. exact H. Qed.

Lemma cspec_bind {A B} (mc : MC St A) (fc : A -> MC St B) (P : assn) (Q1 : A -> assn) (Q : B -> assn) :
  cspec P mc Q1 -> (forall a, cspec (Q1 a) (fc a) Q) -> cspec P (cmbind mc fc) Q.
Proof. intros H1 H2 D h. rewrite RESX_bind. eapply mspec_bind; [apply H1|]. intros ah. apply H2. Qed.

Lemma cspec_choice {A} (a b : MC St A) (P : assn) (Q : A -> assn) : cspec P a Q -> cspec P b Q -> cspec P (cchoice a b) Q.
Proof. intros Ha Hb D h. rewrite RESX_choice. destruct (D h); [apply Ha| apply Hb]. Qed.

Lemma cspec_conseq {A} (mc : MC St A) (P P' : assn) (Q Q' : A -> assn) :
  cspec P mc Q -> (forall s mo, P' s mo -> P s mo) -> (forall a s mo, Q a s mo -> Q' a s mo) -> cspec P' mc Q'.
Proof. intros H HP HQ D h. eapply mspec_conseq; [apply H| exact HP|]. intros ah s mo. apply HQ. Qed.

Lemma cspec_RES {A} (P : assn) (mc : MC St A) (Q : A -> assn) : cspec P mc Q -> forall D h, mspec P (RES D h mc) Q.
Proof.
  intros H D h. rewrite RES_RESX. eapply mspec_bind; [apply H|]. intros ah. apply mspec_ret. intros s mo HQ. exact HQ.
Qed.
End CSpec.

Section CSpecP.
Context {St : Type}.
Local Notation assn := (assn St).

Lemma mspecP_mtag {A} (P : assn) (m : M St A) (Q : A -> assn) h :
  mspecP P m Q -> mspecP P (mtag m h) (fun ah => Q (fst ah)).
Proof.
  intros H s mo HP. unfold mtag, etwfP. apply twfP_hmap. eapply twfP_mono; [exact (H s mo HP)|].
  intros [|[a s1]] mo1 H1 h'; cbn in *; exact H1.
Qed.

Definition cspecP {A} (P : assn) (mc : MC St A) (Q : A -> assn) : Prop :=
  forall D h, mspecP P (RESX D h mc) (fun ah => Q (fst ah)).

Lemma cspecP_lift {A} (P : assn) (m : M St A) (Q : A -> assn) : mspecP P m Q -> cspecP P (clift m) Q.
Proof. intros H D h. rewrite RESX_lift. apply mspecP_mtag. exact H. Qed.

Lemma cspec_cspecP {A} (P : assn) (mc : MC St A) (Q : A -> assn) : cspec P mc Q -> cspecP P mc Q.
Proof. intros H D h. apply mspec_mspecP. apply H. Qed.

Lemma cspecP_ret {A} (a : A) (P : assn) (Q : A -> assn) : (forall s mo, P s mo -> Q a s mo) -> cspecP P (cmret a) Q.
Proof. intros H D h. rewrite RESX_ret. apply mspecP_ret. exact H. Qed.

Lemma cspecP_bind {A B} (mc : MC St A) (fc : A -> MC St B) (P : assn) (Q1 : A -> assn) (Q : B -> assn) :
  cspecP P mc Q1 -> (forall a, cspecP (Q1 a) (fc a) Q) -> cspecP P (cmbind mc fc) Q.
Proof. intros H1 H2 D h. rewrite RESX_bind. eapply mspecP_bind; [apply H1|]. intros ah. apply H2. Qed.

Lemma cspecP_seq {A B} (mc : MC St A) (fc : A -> MC St B) (P R : assn) (Q : B -> assn) :
  cspecP P mc (fun _ => R) -> (forall a, cspecP R (fc a) Q) -> cspecP P (cmbind mc fc) Q.
Proof. intros H1 H2. eapply cspecP_bind; [exact H1| exact H2]. Qed.

Lemma cspecP_choice {A} (a b : MC St A) (P : assn) (Q : A -> assn) : cspecP P a Q -> cspecP P b Q -> cspecP P (cchoice a b) Q.
Proof. intros Ha Hb D h. rewrite RESX_choice. destruct (D h); [apply Ha| apply Hb]. Qed.

Lemma cspecP_conseq {A} (mc : MC St A) (P P' : assn) (Q Q' : A -> assn) :
  cspecP P mc Q -> (forall s mo, P' s mo -> P s mo) -> (forall a s mo, Q a s mo -> Q' a s mo) -> cspecP P' mc Q'.
Proof. intros H HP HQ D h. eapply mspecP_conseq; [apply H| exact HP|]. intros ah s mo. apply HQ. Qed.

Lemma cspecP_pre {A} (mc : MC St A) (P P' : assn) (Q : A -> assn) :
  cspecP P mc Q -> (forall s mo, P' s mo -> P s mo) -> cspecP P' mc Q.
Proof. intros H HP. eapply cspecP_conseq; [exact H| exact HP| auto]. Qed.

Lemma cspecP_if {A} (b : bool) (m1 m2 : MC St A) (P : assn) Q :
  (b = true -> cspecP P m1 Q) -> (b = false -> cspecP P m2 Q) -> cspecP P (if b then m1 else m2) Q.
Proof. intros H1 H2. destruct b; [apply H1| apply H2]; reflexivity. Qed.

Lemma cspecP_post {A} (mc : MC St A) (P : assn) (Q Q' : A -> assn) :
  cspecP P mc Q -> (forall a s mo, Q a s mo -> Q' a s mo) -> cspecP P mc Q'.
Proof. intros H HQ. eapply cspecP_conseq; [exact H| auto| exact HQ]. Qed.

Lemma cspecP_exI {A X} (P : X -> assn) (mc : MC St A) (Q : A -> assn) :
  (forall x, cspecP (P x) mc Q) -> cspecP (fun s mo => exists x, P x s mo) mc Q.
Proof. intros H D h. apply mspecP_exI. intros x. apply H. Qed.

Lemma cspecP_pure {A} (P : assn) (phi : Prop) (mc : MC St A) (Q : A -> assn) :
  (phi -> cspecP P mc Q) -> cspecP (fun s mo => P s mo /\ phi) mc Q.
Proof. intros H D h. apply mspecP_pure. intros Hphi. apply (H Hphi). Qed.

Lemma cspecP_pure_l {A} (P : assn) (phi : Prop) (mc : MC St A) (Q : A -> assn) :
  (phi -> cspecP P mc Q) -> cspecP (fun s mo => phi /\ P s mo) mc Q.
Proof. intros H D h. apply mspecP_pure_l. intros Hphi. apply (H Hphi). Qed.

Lemma cspecP_pointwise {A} (P : assn) (mc : MC St A) (Q : A -> assn) :
  (forall s mo, P s mo -> cspecP (fun s' mo' => s' = s /\ mo' = mo) mc Q) -> cspecP P mc Q.
Proof. intros H D h. apply mspecP_pointwise. intros s mo HP. apply (H s mo HP). Qed.

Lemma cspecP_false {A} (mc : MC St A) (Q : A -> assn) : cspecP (fun _ _ => False) mc Q.
Proof. intros D h s mo []. Qed.

Lemma cspecP_RES {A} (P : assn) (mc : MC St A) (Q : A -> assn) : cspecP P mc Q -> forall D h, mspecP P (RES D h mc) Q.
Proof.
  intros H D h. rewrite RES_RESX. eapply mspecP_bind; [apply H|]. intros ah. apply mspecP_ret. intros s mo HQ. exact HQ.
Qed.
End CSpecP.

Section CSpecL.
Context {St : Type}.
Variable B : Z.
Local Notation assn := (assn St).
Local Notation mspecL := (mspecL B).

Lemma mspecL_mtag {A} (P : assn) (m : M St A) (Q : A -> assn) h :
  mspecL P m Q -> mspecL P (mtag m h) (fun ah => Q (fst ah)).
Proof.
  intros H s mo HP. unfold mtag, etwl. apply twl_hmap. eapply twl_mono; [exact (H s mo HP)|].
  intros [|[a s1]] mo1 H1 h'; cbn in *; exact H1.
Qed.

Definition cspecL {A} (P : assn) (mc : MC St A) (Q : A -> assn) : Prop :=
  forall D h, mspecL P (RESX D h mc) (fun ah => Q (fst ah)).

Lemma cspecL_lift {A} (P : assn) (m : M St A) (Q : A -> assn) : mspecL P m Q -> cspecL P (clift m) Q.
Proof. intros H D h. rewrite RESX_lift. apply mspecL_mtag. exact H. Qed.

Lemma cspecL_ret {A} (a : A) (P : assn) (Q : A -> assn) : (forall s mo, P s mo -> Q a s mo) -> cspecL P (cmret a) Q.
Proof. intros H D h. rewrite RESX_ret. apply mspecL_ret. exact H. Qed.

Lemma cspecL_bind {A C} (mc : MC St A) (fc : A -> MC St C) (P : assn) (Q1 : A -> assn) (Q : C -> assn) :
  cspecL P mc Q1 -> (forall a, cspecL (Q1 a) (fc a) Q) -> cspecL P (cmbind mc fc) Q.
Proof. intros H1 H2 D h. rewrite RESX_bind. eapply mspecL_bind; [apply H1|]. intros ah. apply H2. Qed.

Lemma cspecL_seq {A C} (mc : MC St A) (fc : A -> MC St C) (P R : assn) (Q : C -> assn) :
  cspecL P mc (fun _ => R) -> (forall a, cspecL R (fc a) Q) -> cspecL P (cmbind mc fc) Q.
Proof. intros H1 H2. eapply cspecL_bind; [exact H1| exact H2]. Qed.

Lemma cspecL_choice {A} (a b : MC St A) (P : assn) (Q : A -> assn) : cspecL P a Q -> cspecL P b Q -> cspecL P (cchoice a b) Q.
Proof. intros Ha Hb D h. rewrite RESX_choice. destruct (D h); [apply Ha| apply Hb]. Qed.

Lemma cspecL_conseq {A} (mc : MC St A) (P P' : assn) (Q Q' : A -> assn) :
  cspecL P mc Q -> (forall s mo, P' s mo -> P s mo) -> (forall a s mo, Q a s mo -> Q' a s mo) -> cspecL P' mc Q'.
Proof. intros H HP HQ D h. eapply mspecL_conseq; [apply H| exact HP|]. intros ah s mo. apply HQ. Qed.

Lemma cspecL_pre {A} (mc : MC St A) (P P' : assn) (Q : A -> assn) :
  cspecL P mc Q -> (forall s mo, P' s mo -> P s mo) -> cspecL P' mc Q.
Proof. intros H HP. eapply cspecL_conseq; [exact H| exact HP| auto]. Qed.

Lemma cspecL_if {A} (b : bool) (m1 m2 : MC St A) (P : assn) Q :
  (b = true -> cspecL P m1 Q) -> (b = false -> cspecL P m2 Q) -> cspecL P (if b then m1 else m2) Q.
Proof. intros H1 H2. destruct b; [apply H1| apply H2]; reflexivity. Qed.

Lemma cspecL_post {A} (mc : MC St A) (P : assn) (Q Q' : A -> assn) :
  cspecL P mc Q -> (forall a s mo, Q a s mo -> Q' a s mo) -> cspecL P mc Q'.
Proof. intros H HQ. eapply cspecL_conseq; [exact H| auto| exact HQ]. Qed.

Lemma cspecL_exI {A X} (P : X -> assn) (mc : MC St A) (Q : A -> assn) :
  (forall x, cspecL (P x) mc Q) -> cspecL (fun s mo => exists x, P x s mo) mc Q.
Proof. intros H D h. apply mspecL_exI. intros x. apply H. Qed.

Lemma cspecL_pure {A} (P : assn) (phi : Prop) (mc : MC St A) (Q : A -> assn) :
  (phi -> cspecL P mc Q) -> cspecL (fun s mo => P s mo /\ phi) mc Q.
Proof. intros H D h. apply mspecL_pure. intros Hphi. apply (H Hphi). Qed.

Lemma cspecL_pure_l {A} (P : assn) (phi : Prop) (mc : MC St A) (Q : A -> assn) :
  (phi -> cspecL P mc Q) -> cspecL (fun s mo => phi /\ P s mo) mc Q.
Proof. intros H D h. apply mspecL_pure_l. intros Hphi. apply (H Hphi). Qed.

Lemma cspecL_pointwise {A} (P : assn) (mc : MC St A) (Q : A -> assn) :
  (forall s mo, P s mo -> cspecL (fun s' mo' => s' = s /\ mo' = mo) mc Q) -> cspecL P mc Q.
Proof. intros H D h. apply mspecL_pointwise. intros s mo HP. apply (H s mo HP). Qed.

Lemma cspecL_false {A} (mc : MC St A) (Q : A -> assn) : cspecL (fun _ _ => False) mc Q.
Proof. intros D h s mo []. Qed.

Lemma cspecL_RES {A} (P : assn) (mc : MC St A) (Q : A -> assn) : cspecL P mc Q -> forall D h, mspecL P (RES D h mc) Q.
Proof.
  intros H D h. rewrite RES_RESX. eapply mspecL_bind; [apply H|]. intros ah. apply mspecL_ret. intros s mo HQ. exact HQ.
Qed.
End CSpecL.
