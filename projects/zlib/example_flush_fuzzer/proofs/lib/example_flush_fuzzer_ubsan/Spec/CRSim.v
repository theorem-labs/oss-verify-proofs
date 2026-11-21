(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Lib Require Import ITree Nodes CTree.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Spec Require Import Prelim Monad RSim CMonad.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

Local Notation M := Monad.M.

Lemma tglob_hmap : forall step Phi {R R'} (g : R -> hist -> R') (t : itree node R) h mo,
  tglob step Phi (hmap g t h) mo <-> tglob step Phi t mo.
Proof.
  intros step Phi R R' g t. induction t as [r|n k IH]; intros h mo; cbn; [tauto|].
  split; intros [Hn Hk]; (split; [exact Hn|]); intros rsp mo' evs Hst.
  - exact (proj1 (IH rsp (h ++ [HR rsp]) mo') (Hk _ _ _ Hst)).
  - exact (proj2 (IH rsp (h ++ [HR rsp]) mo') (Hk _ _ _ Hst)).
Qed.

Section GStot.
Context {St : Type}.
Variable step : node -> Model -> resp -> Model -> list event -> Prop.
Variable exit_ : node -> Model -> word -> Model -> Prop.
Variable Phi : node -> Model -> Prop.
Local Notation STOT := (STOT step (fun R0 => texit (R:=R0) step exit_)).










End GStot.

Section CBoth.
Context {S1 S2 : Type}.
Variables (step1 step2 : node -> Model -> resp -> Model -> list event -> Prop).
Variables (exit1 exit2 : node -> Model -> word -> Model -> Prop).
Variables (Phi1 Phi2 : node -> Model -> Prop).
Local Notation rel := (rel S1 S2).
Local Notation rsim := (rsim step1 step2 exit1 exit2 Phi1 Phi2).

Lemma hsim_mtag {Sa Sb A B} stepa stepb exita exitb Phia Phib
      (R : Sa -> Model -> Sb -> Model -> Prop) (ma : M Sa A) (mb : M Sb B) (Q : A -> B -> Sa -> Model -> Sb -> Model -> Prop) ha hb :
  hsim stepa stepb exita exitb Phia Phib R ma mb Q ->
  hsim stepa stepb exita exitb Phia Phib R (mtag ma ha) (mtag mb hb) (fun ah bh => Q (fst ah) (fst bh)).
Proof.
  intros H sa moa sb mob HR Ga Gb. unfold mtag in *.
  apply tglob_hmap in Ga. apply tglob_hmap in Gb.
  destruct (H sa moa sb mob HR Ga Gb) as [HP HE]. split.
  - intros tr ra' moa' Hp. apply tpath_hmap in Hp. destruct Hp as (ra & h' & -> & Hp).
    destruct (HP _ _ _ Hp) as (rb & mob' & Hpb & HRes).
    destruct (tpath_hmap_inv stepb tagr (mb sb) hb mob tr rb mob' Hpb) as (h2' & Hpb').
    exists (tagr rb h2'), mob'. split; [exact Hpb'|].
    destruct ra as [|[a sa']]; destruct rb as [|[b sb']]; cbn in *; auto.
  - intros tr Hx. apply texit_hmap in Hx. apply texit_hmap. exact (HE _ Hx).
Qed.

Lemma rsim_mtag {A B} (R : rel) (m1 : M S1 A) (m2 : M S2 B) (Q : A -> B -> rel) h1 h2 :
  rsim R m1 m2 Q -> rsim R (mtag m1 h1) (mtag m2 h2) (fun ah bh => Q (fst ah) (fst bh)).
Proof.
  intros [H12 H21]. split.
  - apply hsim_mtag. exact H12.
  - eapply hsim_conseq; [apply (hsim_mtag _ _ _ _ _ _ _ _ _ _ h2 h1 H21)| intros; assumption|].
    intros bh ah s2 mo2 s1 mo1 HQ. exact HQ.
Qed.

Definition crsim {A B} (R : rel) (mc1 : MC S1 A) (mc2 : MC S2 B) (Q : A -> B -> rel) : Prop :=
  forall D1 h1 D2 h2, rsim R (RESX D1 h1 mc1) (RESX D2 h2 mc2) (fun ah bh => Q (fst ah) (fst bh)).

Lemma crsim_lift {A B} (R : rel) (m1 : M S1 A) (m2 : M S2 B) (Q : A -> B -> rel) :
  rsim R m1 m2 Q -> crsim R (clift m1) (clift m2) Q.
Proof. intros H D1 h1 D2 h2. rewrite !RESX_lift. apply rsim_mtag. exact H. Qed.

Lemma crsim_ret {A B} (R : rel) (a : A) (b : B) (Q : A -> B -> rel) :
  (forall s1 mo1 s2 mo2, R s1 mo1 s2 mo2 -> Q a b s1 mo1 s2 mo2) -> crsim R (cmret a) (cmret b) Q.
Proof. intros H D1 h1 D2 h2. rewrite !RESX_ret. apply rsim_ret. exact H. Qed.

Lemma crsim_bind {A B A' B'} (R : rel) (mc1 : MC S1 A) (mc2 : MC S2 B) (Q1 : A -> B -> rel)
      (f1 : A -> MC S1 A') (f2 : B -> MC S2 B') (Q : A' -> B' -> rel) :
  crsim R mc1 mc2 Q1 -> (forall a b, crsim (Q1 a b) (f1 a) (f2 b) Q) -> crsim R (cmbind mc1 f1) (cmbind mc2 f2) Q.
Proof.
  intros H1 H2 D1 h1 D2 h2. rewrite !RESX_bind. eapply rsim_bind; [apply H1|]. intros ah bh. apply H2.
Qed.

Lemma crsim_conseq {A B} (R R' : rel) (mc1 : MC S1 A) (mc2 : MC S2 B) (Q Q' : A -> B -> rel) :
  crsim R mc1 mc2 Q ->
  (forall s1 mo1 s2 mo2, R' s1 mo1 s2 mo2 -> R s1 mo1 s2 mo2) ->
  (forall a b s1 mo1 s2 mo2, Q a b s1 mo1 s2 mo2 -> Q' a b s1 mo1 s2 mo2) ->
  crsim R' mc1 mc2 Q'.
Proof. intros H HR HQ D1 h1 D2 h2. eapply rsim_conseq; [apply H| exact HR|]. intros ah bh. apply HQ. Qed.

Lemma crsim_pre {A B} (R R' : rel) (mc1 : MC S1 A) (mc2 : MC S2 B) (Q : A -> B -> rel) :
  crsim R mc1 mc2 Q -> (forall s1 mo1 s2 mo2, R' s1 mo1 s2 mo2 -> R s1 mo1 s2 mo2) -> crsim R' mc1 mc2 Q.
Proof. intros H HR. eapply crsim_conseq; [exact H| exact HR| auto]. Qed.


Lemma crsim_false {A B} (mc1 : MC S1 A) (mc2 : MC S2 B) Q : crsim (fun _ _ _ _ => False) mc1 mc2 Q.
Proof. intros D1 h1 D2 h2. apply rsim_false. Qed.

Lemma crsim_pure {A B} (R : rel) (phi : Prop) (mc1 : MC S1 A) (mc2 : MC S2 B) Q :
  (phi -> crsim R mc1 mc2 Q) -> crsim (fun s1 mo1 s2 mo2 => phi /\ R s1 mo1 s2 mo2) mc1 mc2 Q.
Proof. intros H D1 h1 D2 h2. apply rsim_pure. intros Hphi. apply (H Hphi). Qed.

Lemma crsim_exI {A B X} (R : X -> rel) (mc1 : MC S1 A) (mc2 : MC S2 B) Q :
  (forall x, crsim (R x) mc1 mc2 Q) -> crsim (fun s1 mo1 s2 mo2 => exists x, R x s1 mo1 s2 mo2) mc1 mc2 Q.
Proof. intros H D1 h1 D2 h2. apply rsim_exI. intros x. apply H. Qed.




Lemma crsim_RES {A B} (R : rel) (mc1 : MC S1 A) (mc2 : MC S2 B) (Q : A -> B -> rel) :
  crsim R mc1 mc2 Q -> forall D1 h1 D2 h2, rsim R (RES D1 h1 mc1) (RES D2 h2 mc2) Q.
Proof.
  intros H D1 h1 D2 h2. rewrite !RES_RESX. eapply rsim_bind; [apply H|].
  intros ah bh. apply rsim_ret. intros s1 mo1 s2 mo2 HQ. exact HQ.
Qed.

End CBoth.
