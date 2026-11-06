(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbrW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3.
Import ListNotations.
Import QlEo_c1.Mq0.Exc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G Require T_teq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Unset Keyed Unification.

Notation teq := G.T_teq.teq.
Notation teq_ret := G.T_teq.teq_ret.
Notation teq_vis := G.T_teq.teq_vis.

Section ImplLaws.
Variable segs : list Segment.
Context {node : Type}.
Variable atn : node -> machine_state -> Prop.

Local Notation impl := (QlEo_c1.Mq0.impl segs atn).
Local Notation bind := (QlEo_c1.Mq0.bind node).

#[using="Type"] Lemma impl_bind_ext : forall {A B} (t : itree node A) (f g : A -> itree node B) Q ms,
(forall r ms', impl (f r) Q ms' -> impl (g r) Q ms') ->
impl (bind t f) Q ms -> impl (bind t g) Q ms.
Proof.
induction t as [r|n k IH]; intros f g Q ms Hfg H; cbn [bind] in *.
- apply Hfg. exact H.
- cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp. eapply IH; [exact Hfg | apply Hk].
Qed.

#[using="Type"] Lemma impl_bind_assoc : forall {A B C} (t : itree node A) (f : A -> itree node B) (g : B -> itree node C) Q ms,
impl (bind t (fun x => bind (f x) g)) Q ms -> impl (bind (bind t f) g) Q ms.
Proof.
induction t as [r|n k IH]; intros f g Q ms H; cbn [bind] in *.
- exact H.
- cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp. apply IH. apply Hk.
Qed.

#[using="Type"] Lemma impl_bind_assoc_rev : forall {A B C} (t : itree node A) (f : A -> itree node B) (g : B -> itree node C) Q ms,
impl (bind (bind t f) g) Q ms -> impl (bind t (fun x => bind (f x) g)) Q ms.
Proof.
induction t as [r|n k IH]; intros f g Q ms H; cbn [bind] in *.
- exact H.
- cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp. apply IH. apply Hk.
Qed.

#[using="Type"] Lemma impl_teq : forall {A} (t t' : itree node A) Q ms, teq t t' -> impl t Q ms -> impl t' Q ms.
Proof.
intros A t t' Q ms H. revert ms. induction H as [r|n k k' Hk IH]; intros ms Hi; cbn in *.
- exact Hi.
- eapply evt_mono; [exact Hi|]. intros ms1 [Hat HK]. split; [exact Hat|]. intros rsp. apply IH. apply HK.
Qed.
End ImplLaws.

Section MonadLaws.
Variable segs : list Segment.
Context {St : Type}.
Local Notation implM := (Ql2m.Mq3.implM segs).
Local Open Scope mspec_scope.

#[using="Type"] Lemma implM_assoc : forall {A B C} (a : M St A) (b : A -> M St B) (k : B -> M St C) s Q ms,
implM (mbind a (fun x => mbind (b x) k)) s Q ms -> implM (mbind (mbind a b) k) s Q ms.
Proof.
intros A B C a b k s Q ms H. unfold Ql2m.Mq3.implM, mbind, ebind in *.
apply impl_bind_assoc.
eapply impl_bind_ext; [|exact H]. cbn. intros [|[x s1]] ms' Hx; cbn in *.
- exact Hx.
- exact Hx.
Qed.

#[using="Type"] Lemma implM_assoc_rev : forall {A B C} (a : M St A) (b : A -> M St B) (k : B -> M St C) s Q ms,
implM (mbind (mbind a b) k) s Q ms -> implM (mbind a (fun x => mbind (b x) k)) s Q ms.
Proof.
intros A B C a b k s Q ms H. unfold Ql2m.Mq3.implM, mbind, ebind in *.
apply impl_bind_assoc_rev in H.
eapply impl_bind_ext; [|exact H]. cbn. intros [|[x s1]] ms' Hx; cbn in *.
- exact Hx.
- exact Hx.
Qed.

#[using="Type"] Lemma implM_ret_l : forall {A B} (v : A) (k : A -> M St B) s Q ms,
implM (k v) s Q ms -> implM (mbind (mret v) k) s Q ms.
Proof. intros. exact H. Qed.

#[using="Type"] Lemma implM_ret_l_rev : forall {A B} (v : A) (k : A -> M St B) s Q ms,
implM (mbind (mret v) k) s Q ms -> implM (k v) s Q ms.
Proof. intros. exact H. Qed.

#[using="Type"] Lemma implM_unr_l : forall {A B} (k : A -> M St B) s Q ms, implM (mbind munr k) s Q ms.
Proof. intros. apply implM_unr. Qed.

#[using="Type"] Lemma implM_get_l : forall {B} (k : St -> M St B) s Q ms,
implM (k s) s Q ms -> implM (mbind mget k) s Q ms.
Proof. intros. exact H. Qed.

#[using="Type"] Lemma implM_put_l : forall {B} (s' : St) (k : unit -> M St B) s Q ms,
implM (k tt) s' Q ms -> implM (mbind (mput s') k) s Q ms.
Proof. intros. exact H. Qed.

#[using="Type"] Lemma implM_bind_ext : forall {A B} (a : M St A) (f g : A -> M St B) s Q ms,
(forall x s' ms', implM (f x) s' Q ms' -> implM (g x) s' Q ms') ->
implM (mbind a f) s Q ms -> implM (mbind a g) s Q ms.
Proof.
intros A B a f g s Q ms Hfg H. unfold Ql2m.Mq3.implM, mbind, ebind in *.
eapply impl_bind_ext; [|exact H]. intros [|[x s1]] ms' Hx; cbn in *; [exact Hx|].
apply Hfg. exact Hx.
Qed.

#[using="Type"] Lemma implM_if_false : forall {A} (c : bool) (x y : M St A) s Q ms,
c = false -> implM y s Q ms -> implM (if c then x else y) s Q ms.
Proof. intros A c x y s Q ms -> H. exact H. Qed.
#[using="Type"] Lemma implM_if_true : forall {A} (c : bool) (x y : M St A) s Q ms,
c = true -> implM x s Q ms -> implM (if c then x else y) s Q ms.
Proof. intros A c x y s Q ms -> H. exact H. Qed.
End MonadLaws.

Ltac massoc :=
repeat lazymatch goal with
| |- Ql2m.Mq3.implM _ (mbind (mbind _ _) _) _ _ _ => apply implM_assoc
| |- Ql2m.Mq3.implM _ (mbind (mret _) _) _ _ _ => apply implM_ret_l
end.
