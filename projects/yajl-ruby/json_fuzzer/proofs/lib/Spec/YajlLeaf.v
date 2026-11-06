(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope yprog_scope.

Inductive yleaf {A : Type} : yprog A -> A -> Prop :=
| yl_ret : forall a, yleaf (YRet a) a
| yl_malloc : forall n k r a, yleaf (k r) a -> yleaf (YMalloc n k) a
| yl_realloc : forall p n k r a, yleaf (k r) a -> yleaf (YRealloc p n k) a
| yl_free : forall p k a, yleaf k a -> yleaf (YFree p k) a
| yl_emit : forall bs k a, yleaf k a -> yleaf (YEmit bs k) a.

Lemma yleaf_ret_inv : forall {A} (a b : A), yleaf (YRet a) b -> b = a.
Proof. intros A a b H. inversion H. reflexivity. Qed.

Lemma yleaf_abort_inv : forall {A} (a : A), ~ yleaf (@YAbort A) a.
Proof. intros A a H. inversion H. Qed.

(* [comment removed for export] *)
Lemma yleaf_bind : forall {A B} (m : yprog A) (f : A -> yprog B) a b,
  yleaf m a -> yleaf (f a) b -> yleaf (ybind m f) b.
Proof.
  intros A B m f a b Hm Hf. induction Hm; cbn.
  - exact Hf.
  - eapply yl_malloc; eauto.
  - eapply yl_realloc; eauto.
  - apply yl_free; auto.
  - apply yl_emit; auto.
Qed.

(* [comment removed for export] *)
Lemma yleaf_bind_inv : forall {A B} (m : yprog A) (f : A -> yprog B) b,
  yleaf (ybind m f) b -> exists a, yleaf m a /\ yleaf (f a) b.
Proof.
  intros A B m. induction m as [a0| |n k IH|p n k IH|p k IH|bs k IH]; intros f b HL; cbn in HL.
  - exists a0. split; [apply yl_ret | exact HL].
  - inversion HL.
  - inversion HL; subst.
    match goal with Hk : yleaf (ybind (k ?r) _) _ |- _ =>
      destruct (IH r _ _ Hk) as (aa & Ha1 & Ha2); exists aa; split; [eapply yl_malloc; eauto | exact Ha2] end.
  - inversion HL; subst.
    match goal with Hk : yleaf (ybind (k ?r) _) _ |- _ =>
      destruct (IH r _ _ Hk) as (aa & Ha1 & Ha2); exists aa; split; [eapply yl_realloc; eauto | exact Ha2] end.
  - inversion HL; subst.
    match goal with Hk : yleaf (ybind k _) _ |- _ =>
      destruct (IH _ _ Hk) as (aa & Ha1 & Ha2); exists aa; split; [apply yl_free; auto | exact Ha2] end.
  - inversion HL; subst.
    match goal with Hk : yleaf (ybind k _) _ |- _ =>
      destruct (IH _ _ Hk) as (aa & Ha1 & Ha2); exists aa; split; [apply yl_emit; auto | exact Ha2] end.
Qed.

(* [comment removed for export] *)
Lemma ypost_yleaf : forall {A} (m : yprog A) (Q : A -> Prop) a, ypost m Q -> yleaf m a -> Q a.
Proof.
  intros A m Q a HP HL. induction HL; cbn in HP; auto.
Qed.

(* [comment removed for export] *)
Lemma ysafe_malloc_inv : forall {A} n (k : option yptr -> yprog A) r, ysafe (YMalloc n k) -> ysafe (k r).
Proof. intros A n k r H. exact (H r). Qed.
Lemma ysafe_realloc_inv : forall {A} p n (k : option yptr -> yprog A) r, ysafe (YRealloc p n k) -> ysafe (k r).
Proof. intros A p n k r H. exact (H r). Qed.
Lemma ysafe_free_inv : forall {A} p (k : yprog A), ysafe (YFree p k) -> ysafe k.
Proof. intros A p k H. exact H. Qed.
Lemma ysafe_emit_inv : forall {A} bs (k : yprog A), ysafe (YEmit bs k) -> ysafe k.
Proof. intros A bs k H. exact H. Qed.
Lemma ysafe_assert_inv : forall b (k : yprog unit), ysafe (yassert b ;;; k) -> b = true.
Proof. intros [] k H; [reflexivity | cbn in H; contradiction]. Qed.

(* [comment removed for export] *)
Lemma ysafe_bind_inv : forall {A B} (m : yprog A) (f : A -> yprog B),
  ysafe (ybind m f) -> ysafe m /\ forall a, yleaf m a -> ysafe (f a).
Proof.
  intros A B m. induction m as [a0| |n k IH|p n k IH|p k IH|bs k IH]; intros f HS; cbn in HS |- *.
  - split; [exact I|]. intros a' HL. apply yleaf_ret_inv in HL. subst. exact HS.
  - contradiction.
  - split.
    + intros r. exact (proj1 (IH r f (HS r))).
    + intros a' HL. inversion HL; subst.
      match goal with Hk : yleaf (k ?r) _ |- _ => exact (proj2 (IH r f (HS r)) _ Hk) end.
  - split.
    + intros r. exact (proj1 (IH r f (HS r))).
    + intros a' HL. inversion HL; subst.
      match goal with Hk : yleaf (k ?r) _ |- _ => exact (proj2 (IH r f (HS r)) _ Hk) end.
  - destruct (IH f HS) as [H1 H2]. split; [exact H1|]. intros a' HL. inversion HL; subst. auto.
  - destruct (IH f HS) as [H1 H2]. split; [exact H1|]. intros a' HL. inversion HL; subst. auto.
Qed.

Lemma ysafe_bind : forall {A B} (m : yprog A) (f : A -> yprog B),
  ysafe m -> (forall a, yleaf m a -> ysafe (f a)) -> ysafe (ybind m f).
Proof.
  intros A B m. induction m as [a0| |n k IH|p n k IH|p k IH|bs k IH]; intros f Hm Hf; cbn in Hm |- *.
  - apply Hf. apply yl_ret.
  - contradiction.
  - intros r. apply IH; [exact (Hm r)|]. intros a' HL. apply Hf. eapply yl_malloc; eauto.
  - intros r. apply IH; [exact (Hm r)|]. intros a' HL. apply Hf. eapply yl_realloc; eauto.
  - apply IH; [exact Hm|]. intros a' HL. apply Hf. apply yl_free; auto.
  - apply IH; [exact Hm|]. intros a' HL. apply Hf. apply yl_emit; auto.
Qed.

(* [comment removed for export] *)
Lemma ysafe_has_leaf : forall {A} (m : yprog A), ysafe m -> exists a, yleaf m a.
Proof.
  intros A m. induction m as [a0| |n k IH|p n k IH|p k IH|bs k IH]; intros Hs; cbn in Hs.
  - exists a0. apply yl_ret.
  - contradiction.
  - destruct (IH None (Hs None)) as [a Ha]. exists a. eapply yl_malloc; eauto.
  - destruct (IH None (Hs None)) as [a Ha]. exists a. eapply yl_realloc; eauto.
  - destruct (IH Hs) as [a Ha]. exists a. apply yl_free; auto.
  - destruct (IH Hs) as [a Ha]. exists a. apply yl_emit; auto.
Qed.

(* [comment removed for export] *)
Lemma ypost_of_yleaf : forall {A} (m : yprog A) (Q : A -> Prop),
  ysafe m -> (forall a, yleaf m a -> Q a) -> ypost m Q.
Proof.
  intros A m. induction m as [a0| |n k IH|p n k IH|p k IH|bs k IH]; intros Q Hs HQ; cbn in Hs |- *.
  - apply HQ. apply yl_ret.
  - contradiction.
  - intros r. apply IH; [exact (Hs r)|]. intros a' HL. apply HQ. eapply yl_malloc; eauto.
  - intros r. apply IH; [exact (Hs r)|]. intros a' HL. apply HQ. eapply yl_realloc; eauto.
  - apply IH; [exact Hs|]. intros a' HL. apply HQ. apply yl_free; auto.
  - apply IH; [exact Hs|]. intros a' HL. apply HQ. apply yl_emit; auto.
Qed.
