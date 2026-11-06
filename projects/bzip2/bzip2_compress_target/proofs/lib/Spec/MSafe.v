(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Common Require CfgStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import Monad.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree.Exc.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition nbenign (n : node) (mo : Model) : Prop :=
  match node_input n with
  | Some i => forall eff mo' evs, Specs.syscall_spec i mo (LinuxProcessSem.Monad.Ok eff mo' evs) ->
                evs = [] /\ m_halted mo' = None /\ m_vm_lazy mo' = []
  | None => False   (* [comment removed for export] *)
  end.

Lemma nbenign_nstep : forall n mo i eff mo' evs,
  node_input n = Some i -> nbenign n mo -> Specs.syscall_spec i mo (LinuxProcessSem.Monad.Ok eff mo' evs) ->
  ~ spurious_refusal_cfg CfgStep.kit_cfg i mo eff -> nstep n mo eff mo' evs.
Proof.
  intros n mo i eff mo' evs Hi HB HS Hns. unfold nbenign in HB. rewrite Hi in HB.
  cps_destruct (HB _ _ _ HS) as (-> & _ & _).
  destruct n; cbn in Hi; try discriminate; cbn; rewrite ?Hi; injection Hi as <-; split; auto.
Qed.

Lemma nstep_mm_spec : forall n mo i eff mo' evs,
  node_input n = Some i -> nstep n mo eff mo' evs ->
  evs = [] /\ Specs.syscall_spec i mo (LinuxProcessSem.Monad.Ok eff mo' evs) /\ ~ spurious_refusal_cfg CfgStep.kit_cfg i mo eff.
Proof.
  intros n mo i eff mo' evs Hi HS. destruct n; cbn in Hi; try discriminate; injection Hi as <-; cbn in HS; exact HS.
Qed.
Definition nsafeB (n : node) (mo : Model) : Prop := nsafe n mo /\ nbenign n mo.

(* [comment removed for export] *)

Fixpoint twf {R} (t : itree node R) (mo : Model) (P : R -> Model -> Prop) : Prop :=
  match t with
  | Ret r => P r mo
  | Vis n k => nsafeB n mo /\ forall rsp mo' evs, nstep n mo rsp mo' evs -> twf (k rsp) mo' P
  end.

Lemma twf_mono : forall {R} (t : itree node R) mo (P P' : R -> Model -> Prop),
  twf t mo P -> (forall r mo1, P r mo1 -> P' r mo1) -> twf t mo P'.
Proof.
  intros R t. induction t as [r|n k IH]; intros mo P P' H HP; cbn in *.
  - apply HP. exact H.
  - destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. eapply IH; eauto.
Qed.

Lemma twf_bind : forall {A B} (t : itree node A) (f : A -> itree node B) mo (P : B -> Model -> Prop),
  twf t mo (fun a mo1 => twf (f a) mo1 P) -> twf (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree.bind node t f) mo P.
Proof.
  intros A B t. induction t as [r|n k IH]; intros f mo P H; cbn in *.
  - exact H.
  - destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. apply IH. eapply Hk; eauto.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition etwf {A} (t : itree node (exc A)) (mo : Model) (Q : A -> Model -> Prop) : Prop :=
  twf t mo (fun r mo1 => match r with Unr => False | Ok a => Q a mo1 end).

Lemma etwf_mono : forall {A} (t : itree node (exc A)) mo (Q Q' : A -> Model -> Prop),
  etwf t mo Q -> (forall a mo1, Q a mo1 -> Q' a mo1) -> etwf t mo Q'.
Proof.
  intros A t mo Q Q' H HQ. unfold etwf in *. eapply twf_mono; [exact H|].
  intros [|a] mo1; cbn; auto.
Qed.

Lemma etwf_ebind : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) mo Q,
  etwf t mo (fun a mo1 => etwf (f a) mo1 Q) -> etwf (ebind t f) mo Q.
Proof.
  intros A B t f mo Q H. unfold etwf, ebind in *. apply twf_bind.
  eapply twf_mono; [exact H|]. intros [|a] mo1 Ha; cbn; [destruct Ha| exact Ha].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MSpec.
Context {St : Type}.

Definition assn : Type := St -> Model -> Prop.

Definition mspec {A} (P : assn) (m : M St A) (Q : A -> assn) : Prop :=
  forall s mo, P s mo -> etwf (m s) mo (fun p mo' => Q (fst p) (snd p) mo').

Lemma mspec_ret {A} (a : A) (P : assn) (Q : A -> assn) :
  (forall s mo, P s mo -> Q a s mo) -> mspec P (mret a) Q.
Proof. intros H s mo HP. cbn. apply H. exact HP. Qed.

Lemma mspec_bind {A B} (m : M St A) (f : A -> M St B) (P : assn) (Q1 : A -> assn) (Q : B -> assn) :
  mspec P m Q1 -> (forall a, mspec (Q1 a) (f a) Q) -> mspec P (mbind m f) Q.
Proof.
  intros Hm Hf s mo HP. unfold mbind. apply etwf_ebind.
  eapply etwf_mono; [exact (Hm s mo HP)|]. intros [a s1] mo1 H1. cbn in *. exact (Hf a s1 mo1 H1).
Qed.

Lemma mspec_conseq {A} (m : M St A) (P P' : assn) (Q Q' : A -> assn) :
  mspec P m Q -> (forall s mo, P' s mo -> P s mo) -> (forall a s mo, Q a s mo -> Q' a s mo) -> mspec P' m Q'.
Proof.
  intros Hm HP HQ s mo HP'. eapply etwf_mono; [exact (Hm s mo (HP _ _ HP'))|].
  intros [a s1] mo1; cbn; auto.
Qed.

Lemma mspec_pre {A} (m : M St A) (P P' : assn) (Q : A -> assn) :
  mspec P m Q -> (forall s mo, P' s mo -> P s mo) -> mspec P' m Q.
Proof. intros Hm HP. eapply mspec_conseq; eauto. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma mspec_get (P : assn) : mspec P mget (fun s' s mo => s' = s /\ P s mo).
Proof. intros s mo HP. cbn. auto. Qed.

(* [comment removed for export] *)

Lemma mspec_upd (P : assn) (f : St -> St) : mspec P (mupd f) (fun _ s mo => exists s0, s = f s0 /\ P s0 mo).
Proof. intros s mo HP. cbn. eauto. Qed.

Lemma mspec_upd' (P : assn) (Q : unit -> assn) (f : St -> St) :
  (forall s mo, P s mo -> Q tt (f s) mo) -> mspec P (mupd f) Q.
Proof. intros H s mo HP. cbn. apply H. exact HP. Qed.

(* [comment removed for export] *)
Lemma mspec_sys {A} (n : node) (dec : resp -> option A) (P : assn) (Q : A -> assn) :
  (forall s mo, P s mo ->
     nsafeB n mo /\
     forall rsp mo' evs, nstep n mo rsp mo' evs -> exists a, dec rsp = Some a /\ Q a s mo') ->
  mspec P (msys n dec) Q.
Proof.
  intros H s mo HP. destruct (H s mo HP) as [Hs Hk]. unfold msys. cbn. split; [exact Hs|].
  intros rsp mo' evs Hst. cps_destruct (Hk rsp mo' evs Hst) as (a & -> & HQ). exact HQ.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mspec_pointwise {A} (P : assn) (m : M St A) (Q : A -> assn) :
  (forall s mo, P s mo -> mspec (fun s' mo' => s' = s /\ mo' = mo) m Q) -> mspec P m Q.
Proof. intros H s mo HP. apply (H s mo HP). auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mspec_seq {A B} (m : M St A) (f : A -> M St B) (P R : assn) (Q : B -> assn) :
  mspec P m (fun _ => R) -> (forall a, mspec R (f a) Q) -> mspec P (mbind m f) Q.
Proof. intros Hm Hf. eapply mspec_bind; [exact Hm|]. intros a. apply Hf. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

End MSpec.
End ACeilS1.


Arguments assn St : clear implicits.
Arguments mspec {St A} P m Q.
