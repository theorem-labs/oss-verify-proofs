(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Monad MSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint treach {R : Type} (t : itree node R) (mo : Model) (P : R -> Model -> Prop) : Prop :=
  match t with
  | Ret r => P r mo
  | Vis n k => exists rsp mo' evs, nstep n mo rsp mo' evs /\ treach (k rsp) mo' P
  end.

Lemma treach_mono : forall {R} (t : itree node R) mo (P P' : R -> Model -> Prop),
  treach t mo P -> (forall r mo', P r mo' -> P' r mo') -> treach t mo P'.
Proof.
  intros R t; induction t as [r | n k IH]; intros mo P P' H HP; cbn in *.
  - apply HP. exact H.
  - destruct H as (rsp & mo' & evs & Hst & Hk). exists rsp, mo', evs. split; [exact Hst|]. eapply IH; [exact Hk| exact HP].
Qed.

Lemma treach_bind : forall {A B} (t : itree node A) (f : A -> itree node B) mo (P : B -> Model -> Prop),
  treach t mo (fun a mo1 => treach (f a) mo1 P) -> treach (ITree.bind node t f) mo P.
Proof.
  intros A B t; induction t as [r | n k IH]; intros f mo P H; cbn in *.
  - exact H.
  - destruct H as (rsp & mo' & evs & Hst & Hk). exists rsp, mo', evs. split; [exact Hst|]. apply IH. exact Hk.
Qed.

(* [comment removed for export] *)
Lemma treach_twf : forall {R} (t : itree node R) mo (P Q : R -> Model -> Prop),
  treach t mo P -> twf t mo Q -> treach t mo (fun r mo' => P r mo' /\ Q r mo').
Proof.
  intros R t; induction t as [r | n k IH]; intros mo P Q H W; cbn in *.
  - auto.
  - destruct H as (rsp & mo' & evs & Hst & Hk). destruct W as [_ Wk]. exists rsp, mo', evs. split; [exact Hst|].
    apply IH; [exact Hk| eapply Wk; exact Hst].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MReach.
Context {St : Type}.
Local Notation MS := (Monad.M St).

Definition mreach {A} (P : assn St) (m : MS A) (Q : A -> assn St) : Prop :=
  forall s mo, P s mo -> treach (m s) mo (fun p mo' => match p with Unr => False | Ok x => Q (fst x) (snd x) mo' end).

Lemma mreach_ret {A} (a : A) (P : assn St) (Q : A -> assn St) :
  (forall s mo, P s mo -> Q a s mo) -> mreach P (mret a) Q.
Proof. intros H s mo HP. cbn. apply H. exact HP. Qed.

Lemma mreach_bind {A B} (m : MS A) (f : A -> MS B) (P : assn St) (Q1 : A -> assn St) (Q : B -> assn St) :
  mreach P m Q1 -> (forall a, mreach (Q1 a) (f a) Q) -> mreach P (mbind m f) Q.
Proof.
  intros Hm Hf s mo HP. unfold mbind, ebind. apply treach_bind.
  eapply treach_mono; [exact (Hm s mo HP)|]. intros [|[a s1]] mo1 H1; cbn in *; [destruct H1|]. exact (Hf a s1 mo1 H1).
Qed.

Lemma mreach_conseq {A} (m : MS A) (P P' : assn St) (Q Q' : A -> assn St) :
  mreach P m Q -> (forall s mo, P' s mo -> P s mo) -> (forall a s mo, Q a s mo -> Q' a s mo) -> mreach P' m Q'.
Proof.
  intros Hm HP HQ s mo HP'. eapply treach_mono; [exact (Hm s mo (HP _ _ HP'))|].
  intros [|[a s1]] mo1; cbn; auto.
Qed.

Lemma mreach_pre {A} (m : MS A) (P P' : assn St) (Q : A -> assn St) :
  mreach P m Q -> (forall s mo, P' s mo -> P s mo) -> mreach P' m Q.
Proof. intros Hm HP. eapply mreach_conseq; eauto. Qed.

Lemma mreach_post {A} (m : MS A) (P : assn St) (Q Q' : A -> assn St) :
  mreach P m Q -> (forall a s mo, Q a s mo -> Q' a s mo) -> mreach P m Q'.
Proof. intros Hm HQ. eapply mreach_conseq; eauto. Qed.

Lemma mreach_get (P : assn St) : mreach P mget (fun s' s mo => s' = s /\ P s mo).
Proof. intros s mo HP. cbn. auto. Qed.

Lemma mreach_upd (P : assn St) (Q : unit -> assn St) (f : St -> St) :
  (forall s mo, P s mo -> Q tt (f s) mo) -> mreach P (mupd f) Q.
Proof. intros H s mo HP. cbn. apply H. exact HP. Qed.

Lemma mreach_if {A} (b : bool) (m1 m2 : MS A) (P : assn St) Q :
  (b = true -> mreach P m1 Q) -> (b = false -> mreach P m2 Q) -> mreach P (if b then m1 else m2) Q.
Proof. intros H1 H2. destruct b; auto. Qed.

Lemma mreach_false {A} (m : MS A) (Q : A -> assn St) : mreach (fun _ _ => False) m Q.
Proof. intros s mo []. Qed.

(* [comment removed for export] *)
Lemma mreach_sys {A} (n : node) (dec : resp -> option A) (P : assn St) (Q : A -> assn St) :
  (forall s mo, P s mo -> exists rsp mo' evs a, nstep n mo rsp mo' evs /\ dec rsp = Some a /\ Q a s mo') ->
  mreach P (msys n dec) Q.
Proof.
  intros H s mo HP. destruct (H s mo HP) as (rsp & mo' & evs & a & Hst & Hd & HQ).
  unfold msys, enode. cbn. exists rsp, mo', evs. split; [exact Hst|]. rewrite Hd. cbn. exact HQ.
Qed.

(* [comment removed for export] *)
Lemma mreach_pointwise {A} (m : MS A) (P : assn St) (Q : A -> assn St) :
  (forall s0 mo0, P s0 mo0 -> mreach (fun s mo => s = s0 /\ mo = mo0) m Q) -> mreach P m Q.
Proof. intros H s mo HP. apply (H s mo HP). auto. Qed.

End MReach.
Arguments mreach {St A} P m Q.
