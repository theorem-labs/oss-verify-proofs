(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim Monad.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

Section ImplLaws.
  Variable segs : list Segment.
  Context {node : Type}.
  Variable atn : node -> machine_state -> Prop.

  Local Notation impl := (ITree.impl segs atn).
  Local Notation bind := (ITree.bind node).

  Lemma impl_bind_ext : forall {A B} (t : itree node A) (f g : A -> itree node B) Q ms,
    (forall r ms', impl (f r) Q ms' -> impl (g r) Q ms') ->
    impl (bind t f) Q ms -> impl (bind t g) Q ms.
  Proof.
    induction t as [r|n k IH|kc IHc]; intros f g Q ms Hfg H; cbn [bind] in *.
    - apply Hfg. exact H.
    - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
      intros rsp. eapply IH; [exact Hfg | apply Hk].
    - cbn in H |- *. destruct H as [z H]. exists z. eapply IHc; [exact Hfg | exact H].
  Qed.

  Lemma impl_bind_assoc : forall {A B C} (t : itree node A) (f : A -> itree node B) (g : B -> itree node C) Q ms,
    impl (bind t (fun x => bind (f x) g)) Q ms -> impl (bind (bind t f) g) Q ms.
  Proof.
    induction t as [r|n k IH|kc IHc]; intros f g Q ms H; cbn [bind] in *.
    - exact H.
    - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
      intros rsp. apply IH. apply Hk.
    - cbn in H |- *. destruct H as [z H]. exists z. apply IHc. exact H.
  Qed.

  Lemma impl_bind_assoc_rev : forall {A B C} (t : itree node A) (f : A -> itree node B) (g : B -> itree node C) Q ms,
    impl (bind (bind t f) g) Q ms -> impl (bind t (fun x => bind (f x) g)) Q ms.
  Proof.
    induction t as [r|n k IH|kc IHc]; intros f g Q ms H; cbn [bind] in *.
    - exact H.
    - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
      intros rsp. apply IH. apply Hk.
    - cbn in H |- *. destruct H as [z H]. exists z. apply IHc. exact H.
  Qed.

  Inductive teq {A} : itree node A -> itree node A -> Prop :=
  | teq_ret : forall r, teq (Ret r) (Ret r)
  | teq_vis : forall n k k', (forall x, teq (k x) (k' x)) -> teq (Vis n k) (Vis n k').

  Lemma impl_teq : forall {A} (t t' : itree node A) Q ms, teq t t' -> impl t Q ms -> impl t' Q ms.
  Proof.
    intros A t t' Q ms H. revert ms. induction H as [r|n k k' Hk IH]; intros ms Hi; cbn in *.
    - exact Hi.
    - eapply evt_mono; [exact Hi|]. intros ms1 [Hat HK]. split; [exact Hat|]. intros rsp. apply IH. apply HK.
  Qed.
End ImplLaws.

Section MonadLaws.
  Variable segs : list Segment.
  Context {St : Type}.
  Local Notation implM := (Monad.implM segs).
  Local Open Scope mspec_scope.

  Lemma implM_assoc : forall {A B C} (a : M St A) (b : A -> M St B) (k : B -> M St C) s Q ms,
    implM (mbind a (fun x => mbind (b x) k)) s Q ms -> implM (mbind (mbind a b) k) s Q ms.
  Proof.
    intros A B C a b k s Q ms H. unfold Monad.implM, mbind, ebind in *.
    apply impl_bind_assoc.
    eapply impl_bind_ext; [|exact H]. cbn. intros [|[x s1]] ms' Hx; cbn in *.
    - exact Hx.
    - exact Hx.
  Qed.

  Lemma implM_assoc_rev : forall {A B C} (a : M St A) (b : A -> M St B) (k : B -> M St C) s Q ms,
    implM (mbind (mbind a b) k) s Q ms -> implM (mbind a (fun x => mbind (b x) k)) s Q ms.
  Proof.
    intros A B C a b k s Q ms H. unfold Monad.implM, mbind, ebind in *.
    apply impl_bind_assoc_rev in H.
    eapply impl_bind_ext; [|exact H]. cbn. intros [|[x s1]] ms' Hx; cbn in *.
    - exact Hx.
    - exact Hx.
  Qed.

  Lemma implM_ret_l : forall {A B} (v : A) (k : A -> M St B) s Q ms,
    implM (k v) s Q ms -> implM (mbind (mret v) k) s Q ms.
  Proof. intros. exact H. Qed.

  Lemma implM_ret_l_rev : forall {A B} (v : A) (k : A -> M St B) s Q ms,
    implM (mbind (mret v) k) s Q ms -> implM (k v) s Q ms.
  Proof. intros. exact H. Qed.

  Lemma implM_unr_l : forall {A B} (k : A -> M St B) s Q ms, implM (mbind munr k) s Q ms.
  Proof. intros. apply implM_unr. Qed.

  Lemma implM_get_l : forall {B} (k : St -> M St B) s Q ms,
    implM (k s) s Q ms -> implM (mbind mget k) s Q ms.
  Proof. intros. exact H. Qed.

  Lemma implM_put_l : forall {B} (s' : St) (k : unit -> M St B) s Q ms,
    implM (k tt) s' Q ms -> implM (mbind (mput s') k) s Q ms.
  Proof. intros. exact H. Qed.

  Lemma implM_bind_ext : forall {A B} (a : M St A) (f g : A -> M St B) s Q ms,
    (forall x s' ms', implM (f x) s' Q ms' -> implM (g x) s' Q ms') ->
    implM (mbind a f) s Q ms -> implM (mbind a g) s Q ms.
  Proof.
    intros A B a f g s Q ms Hfg H. unfold Monad.implM, mbind, ebind in *.
    eapply impl_bind_ext; [|exact H]. intros [|[x s1]] ms' Hx; cbn in *; [exact Hx|].
    apply Hfg. exact Hx.
  Qed.

  Lemma implM_if_false : forall {A} (c : bool) (x y : M St A) s Q ms,
    c = false -> implM y s Q ms -> implM (if c then x else y) s Q ms.
  Proof. intros A c x y s Q ms -> H. exact H. Qed.
  Lemma implM_if_true : forall {A} (c : bool) (x y : M St A) s Q ms,
    c = true -> implM x s Q ms -> implM (if c then x else y) s Q ms.
  Proof. intros A c x y s Q ms -> H. exact H. Qed.
End MonadLaws.

Ltac massoc :=
  repeat lazymatch goal with
  | |- Monad.implM _ (mbind (mbind _ _) _) _ _ _ => apply implM_assoc
  | |- Monad.implM _ (mbind (mret _) _) _ _ _ => apply implM_ret_l
  end.
