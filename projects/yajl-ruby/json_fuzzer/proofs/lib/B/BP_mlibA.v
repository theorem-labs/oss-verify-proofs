(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem ITree Nodes.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import ExecA ITreeA MonadA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import Printf_mlib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section ImplLawsA.
  Variable segs : list Segment.
  Context {node : Type}.
  Variable atn : (acc -> Prop) -> node -> machine_state -> Prop.
  Variable P : acc -> Prop.

  Local Notation impl := (implA segs atn P).
  Local Notation bind := (ITree.bind node).

  Lemma implA_bind_ext : forall {A B} (t : itree node A) (f g : A -> itree node B) Q ms,
    (forall r ms', impl (f r) Q ms' -> impl (g r) Q ms') ->
    impl (bind t f) Q ms -> impl (bind t g) Q ms.
  Proof.
    induction t as [r|n k IH]; intros f g Q ms Hfg H; cbn [bind] in *.
    - apply Hfg. exact H.
    - cbn in H |- *. eapply evtA_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
      intros rsp. eapply IH; [exact Hfg | apply Hk].
  Qed.

  Lemma implA_bind_assoc : forall {A B C} (t : itree node A) (f : A -> itree node B) (g : B -> itree node C) Q ms,
    impl (bind t (fun x => bind (f x) g)) Q ms -> impl (bind (bind t f) g) Q ms.
  Proof.
    induction t as [r|n k IH]; intros f g Q ms H; cbn [bind] in *.
    - exact H.
    - cbn in H |- *. eapply evtA_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
      intros rsp. apply IH. apply Hk.
  Qed.

  Lemma implA_bind_assoc_rev : forall {A B C} (t : itree node A) (f : A -> itree node B) (g : B -> itree node C) Q ms,
    impl (bind (bind t f) g) Q ms -> impl (bind t (fun x => bind (f x) g)) Q ms.
  Proof.
    induction t as [r|n k IH]; intros f g Q ms H; cbn [bind] in *.
    - exact H.
    - cbn in H |- *. eapply evtA_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
      intros rsp. apply IH. apply Hk.
  Qed.

  Lemma implA_teq : forall {A} (t t' : itree node A) Q ms, teq t t' -> impl t Q ms -> impl t' Q ms.
  Proof.
    intros A t t' Q ms E. revert Q ms. induction E as [r|n k k' Hk IH]; intros Q ms H; [exact H|].
    cbn in H |- *. eapply evtA_mono; [exact H|]. intros ms1 [Hat Hk']. split; [exact Hat|].
    intros rsp. apply IH. apply Hk'.
  Qed.
End ImplLawsA.

Section MonadLawsA.
  Variable segs : list Segment.
  Context {St : Type}.
  Variable P : acc -> Prop.
  Local Notation implMA := (implMA segs P (St:=St)).

  Lemma implMA_assoc : forall {A B C} (a : M St A) (b : A -> M St B) (k : B -> M St C) s Q ms,
    implMA (mbind a (fun x => mbind (b x) k)) s Q ms -> implMA (mbind (mbind a b) k) s Q ms.
  Proof.
    intros A B C a b k s Q ms H. unfold MonadA.implMA, mbind, ebind in *.
    apply implA_bind_assoc.
    eapply implA_bind_ext; [|exact H]. cbn. intros [|[x s1]] ms' Hx; cbn in *; exact Hx.
  Qed.
  Lemma implMA_assoc_rev : forall {A B C} (a : M St A) (b : A -> M St B) (k : B -> M St C) s Q ms,
    implMA (mbind (mbind a b) k) s Q ms -> implMA (mbind a (fun x => mbind (b x) k)) s Q ms.
  Proof.
    intros A B C a b k s Q ms H. unfold MonadA.implMA, mbind, ebind in *.
    apply implA_bind_assoc_rev in H.
    eapply implA_bind_ext; [|exact H]. cbn. intros [|[x s1]] ms' Hx; cbn in *; exact Hx.
  Qed.
  Lemma implMA_ret_l : forall {A B} (v : A) (k : A -> M St B) s Q ms,
    implMA (k v) s Q ms -> implMA (mbind (mret v) k) s Q ms.
  Proof. intros. exact H. Qed.
  Lemma implMA_ret_l_rev : forall {A B} (v : A) (k : A -> M St B) s Q ms,
    implMA (mbind (mret v) k) s Q ms -> implMA (k v) s Q ms.
  Proof. intros. exact H. Qed.
  Lemma implMA_unr_l : forall {A B} (k : A -> M St B) s Q ms, implMA (mbind munr k) s Q ms.
  Proof. intros. apply implMA_unr. Qed.
  Lemma implMA_get_l : forall {B} (k : St -> M St B) s Q ms,
    implMA (k s) s Q ms -> implMA (mbind mget k) s Q ms.
  Proof. intros. exact H. Qed.
  Lemma implMA_put_l : forall {B} (s' : St) (k : unit -> M St B) s Q ms,
    implMA (k tt) s' Q ms -> implMA (mbind (mput s') k) s Q ms.
  Proof. intros. exact H. Qed.
  Lemma implMA_bind_ext : forall {A B} (a : M St A) (f g : A -> M St B) s Q ms,
    (forall x s' ms', implMA (f x) s' Q ms' -> implMA (g x) s' Q ms') ->
    implMA (mbind a f) s Q ms -> implMA (mbind a g) s Q ms.
  Proof.
    intros A B a f g s Q ms Hfg H. unfold MonadA.implMA, mbind, ebind in *.
    eapply implA_bind_ext; [|exact H]. intros [|[x s1]] ms' Hx; cbn in *; [exact Hx|].
    apply Hfg. exact Hx.
  Qed.
  Lemma implMA_if_false : forall {A} (c : bool) (x y : M St A) s Q ms,
    c = false -> implMA y s Q ms -> implMA (if c then x else y) s Q ms.
  Proof. intros A c x y s Q ms -> H. exact H. Qed.
  Lemma implMA_if_true : forall {A} (c : bool) (x y : M St A) s Q ms,
    c = true -> implMA x s Q ms -> implMA (if c then x else y) s Q ms.
  Proof. intros A c x y s Q ms -> H. exact H. Qed.
End MonadLawsA.

(* [comment removed for export] *)
End RC__1.
Ltac massocA :=
  repeat lazymatch goal with
  | |- MonadA.implMA _ _ (mbind (mbind _ _) _) _ _ _ => apply implMA_assoc
  | |- MonadA.implMA _ _ (mbind (mret _) _) _ _ _ => apply implMA_ret_l
  end.
