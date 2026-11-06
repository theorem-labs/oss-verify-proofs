(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import ITree Nodes NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Monad MSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

Section RC__.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section TALL.
Variable N : node -> Model -> resp -> Model -> list event -> Prop.

Fixpoint tall {R} (t : itree node R) (mo : Model) (Q : R -> Model -> Prop) : Prop :=
  match t with
  | Ret r => Q r mo
  | Vis n k => forall rsp mo' evs, N n mo rsp mo' evs -> tall (k rsp) mo' Q
  end.

Lemma tall_mono {R} (t : itree node R) : forall mo (Q Q' : R -> Model -> Prop),
  tall t mo Q -> (forall r mo', Q r mo' -> Q' r mo') -> tall t mo Q'.
Proof.
  induction t as [r | n k IH]; intros mo Q Q' H HQ; cbn in *; [apply HQ; exact H|].
  intros rsp mo' evs Hst. eapply IH; [exact (H rsp mo' evs Hst) | exact HQ].
Qed.

Lemma tall_trivial {R} (t : itree node R) : forall mo (Q : R -> Model -> Prop),
  (forall r mo', Q r mo') -> tall t mo Q.
Proof. induction t as [r | n k IH]; intros mo Q HQ; cbn; auto. Qed.

Lemma tall_conj {R} (t : itree node R) : forall mo (Q1 Q2 : R -> Model -> Prop),
  tall t mo Q1 -> tall t mo Q2 -> tall t mo (fun r mo' => Q1 r mo' /\ Q2 r mo').
Proof.
  induction t as [r | n k IH]; intros mo Q1 Q2 H1 H2; cbn in *; [split; assumption|].
  intros rsp mo' evs Hst. apply IH; [exact (H1 _ _ _ Hst) | exact (H2 _ _ _ Hst)].
Qed.

Lemma tall_bind {A B} (t : itree node A) (f : A -> itree node B) : forall mo (Q : B -> Model -> Prop),
  tall t mo (fun a mo' => tall (f a) mo' Q) -> tall (ITree.bind node t f) mo Q.
Proof.
  induction t as [a | n k IH]; intros mo Q H; cbn in *; [exact H|].
  intros rsp mo' evs Hst. apply IH. exact (H _ _ _ Hst).
Qed.

Lemma tall_bind_inv {A B} (t : itree node A) (f : A -> itree node B) : forall mo (Q : B -> Model -> Prop),
  tall (ITree.bind node t f) mo Q -> tall t mo (fun a mo' => tall (f a) mo' Q).
Proof.
  induction t as [a | n k IH]; intros mo Q H; cbn in *; [exact H|].
  intros rsp mo' evs Hst. apply IH. exact (H _ _ _ Hst).
Qed.
End TALL.

Lemma tall_antitone (N N' : node -> Model -> resp -> Model -> list event -> Prop) {R} (t : itree node R) :
  (forall n mo rsp mo' evs, N' n mo rsp mo' evs -> N n mo rsp mo' evs) ->
  forall mo Q, tall N t mo Q -> tall N' t mo Q.
Proof.
  intros SUB. induction t as [r | n k IH]; intros mo Q H; cbn in *; [exact H|].
  intros rsp mo' evs Hst. apply IH. exact (H _ _ _ (SUB _ _ _ _ _ Hst)).
Qed.

Lemma tall_of_twf {R} (t : itree node R) : forall mo Q, twf t mo Q -> tall nstep t mo Q.
Proof.
  induction t as [r | n k IH]; intros mo Q H; cbn in *; [exact H|].
  destruct H as [_ Hk]. intros rsp mo' evs Hst. apply IH. exact (Hk _ _ _ Hst).
Qed.

(* [comment removed for export] *)
Definition ctall {A} (t : itree node (exc A)) (mo : Model) (Q : A -> Model -> Prop) : Prop :=
  tall (nstep_cfg acfg) t mo (fun r mo' => match r with Unr => True | Ok a => Q a mo' end).

Lemma ctall_of_etwf {A} (t : itree node (exc A)) mo Q : etwf t mo Q -> ctall t mo Q.
Proof.
  intros H. unfold ctall, etwf in *. apply (tall_antitone nstep); [intros; eapply nstep_cfg_sub; eassumption|].
  eapply tall_mono; [apply tall_of_twf; exact H|]. intros [|a] mo'; cbn; tauto.
Qed.

Lemma ctall_mono {A} (t : itree node (exc A)) mo (Q Q' : A -> Model -> Prop) :
  ctall t mo Q -> (forall a mo', Q a mo' -> Q' a mo') -> ctall t mo Q'.
Proof. intros H HQ. unfold ctall in *. eapply tall_mono; [exact H|]. intros [|a] mo'; cbn; auto. Qed.

Lemma ctall_conj {A} (t : itree node (exc A)) mo (Q1 Q2 : A -> Model -> Prop) :
  ctall t mo Q1 -> ctall t mo Q2 -> ctall t mo (fun a mo' => Q1 a mo' /\ Q2 a mo').
Proof.
  intros H1 H2. unfold ctall in *. eapply tall_mono; [apply (tall_conj _ _ _ _ _ H1 H2)|].
  intros [|a] mo'; cbn; tauto.
Qed.

Lemma ctall_ebind {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) mo Q :
  ctall t mo (fun a mo' => ctall (f a) mo' Q) -> ctall (ebind t f) mo Q.
Proof.
  intros H. unfold ctall, ebind in *. apply tall_bind. eapply tall_mono; [exact H|].
  intros [|a] mo'; cbn; [intros _; exact I | intros H'; exact H'].
Qed.

End RC__.
