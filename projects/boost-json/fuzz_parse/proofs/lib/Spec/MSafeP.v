(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Monad.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "3h5LinuxProcessSemanticsfLinuxProcessSem5State05Model37Corelib4Init9Datatypesj54unit37Corelib4Init5Logicl43andl42eql42ex99OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MSafeP5NSAFE5MSpec~~~~~~n84assnn85mspec79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec5Monad~~~~~~t14mupdj52tt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Nodes~~~~~~hha4node" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.

Section NSAFE.
Variable nsafe : ltac2:(zQ "20!ie!hl6>0$1>0$0P").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint twf {R} (t : itree node R) (mo : Model) (P : R -> Model -> Prop) : Prop :=
  match t with
  | Ret r => P r mo
  | Vis n k => nsafe n mo /\ forall rsp mo' evs, nstep n mo rsp mo' evs -> twf (k rsp) mo' P
  end.

Lemma twf_mono : forall {R} (t : itree node R) mo (P P' : R -> Model -> Prop),
  twf t mo P -> (forall r mo1, P r mo1 -> P' r mo1) -> twf t mo P'.
Proof.
  intros R t. induction t as [r|n k IH]; intros mo P P' H HP; cbn in *.
  - apply HP. exact H.
  - destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. eapply IH; eauto.
Qed.

Lemma twf_bind : forall {A B} (t : itree node A) (f : A -> itree node B) mo (P : B -> Model -> Prop),
  twf t mo (fun a mo1 => twf (f a) mo1 P) -> twf (ITree.bind node t f) mo P.
Proof.
  intros A B t. induction t as [r|n k IH]; intros f mo P H; cbn in *.
  - exact H.
  - destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. apply IH. eapply Hk; eauto.
Qed.

Lemma twf_tsafe : forall {R} (t : itree node R) mo P, twf t mo P -> tsafe nstep nsafe t mo.
Proof.
  intros R t. induction t as [r|n k IH]; intros mo P H; cbn in *; [exact I|].
  destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. eapply IH. eapply Hk; eauto.
Qed.

Lemma twf_tpath : forall {R} (t : itree node R) mo P tr r mo',
  twf t mo P -> tpath nstep t mo tr r mo' -> P r mo'.
Proof.
  intros R t. induction t as [r0|n k IH]; intros mo P tr r mo' H Hp; cbn in *.
  - destruct Hp as (<- & -> & ->). exact H.
  - destruct H as [_ Hk]. destruct Hp as (rsp & mo1 & evs & tr' & Hst & Hp & _).
    eapply IH; [eapply Hk; exact Hst| exact Hp].
Qed.

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

Section MSpec.
Context {St : Type}.

Definition assn : ltac2:(zQ "00T") := ltac2:(zQ "10!ie>0?2St>0$0P").

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

Lemma mspec_upd : ltac2:(zQ "80!kd!m8!me!n3!ie!s2!s9!hge>1P$5>1f>0?2St?2St@4$6$0^2@2$7?2St^1\0$0\1s?2St\2mo$4@2$3?2St\2s0?2St@2$1@3$2?2St^3@1^5^1@2^6^1^2").
Proof. intros P f. intros s mo HP. cbn. eauto. Qed.

Lemma mspec_upd' : ltac2:(zQ "60!kd!s2!hh5!ie!s9!hge>1P$1>1Q>0$0$1>1f>0?2St?2St>0>1s?2St>2mo$3>0@2^5^2^1@3^5$2@1^4^3^2@4$4$0^4@2$5?2St^2^3").
Proof. intros P Q f. intros H s mo HP. cbn. apply H. exact HP. Qed.

(* [comment removed for export] *)
Lemma mspec_sys {A} (n : node) (dec : resp -> option A) (P : assn) (Q : A -> assn) :
  (forall s mo, P s mo ->
     nsafe n mo /\
     forall rsp mo' evs, nstep n mo rsp mo' evs -> exists a, dec rsp = Some a /\ Q a s mo') ->
  mspec P (msys n dec) Q.
Proof.
  intros H s mo HP. destruct (H s mo HP) as [Hs Hk]. unfold msys. cbn. split; [exact Hs|].
  intros rsp mo' evs Hst. destruct (Hk rsp mo' evs Hst) as (a & -> & HQ). exact HQ.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mspec_pointwise {A} (P : assn) (m : M St A) (Q : A -> assn) :
  (forall s mo, P s mo -> mspec (fun s' mo' => s' = s /\ mo' = mo) m Q) -> mspec P m Q.
Proof. intros H s mo HP. apply (H s mo HP). auto. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mspec_seq {A B} (m : M St A) (f : A -> M St B) (P R : assn) (Q : B -> assn) :
  mspec P m (fun _ => R) -> (forall a, mspec R (f a) Q) -> mspec P (mbind m f) Q.
Proof. intros Hm Hf. eapply mspec_bind; [exact Hm|]. intros a. apply Hf. Qed.

(* [comment removed for export] *)

End MSpec.
End NSAFE.

Arguments assn St : clear implicits.
Arguments mspec nsafe {St A} P m Q.
Arguments twf nsafe {R} t mo P.
Arguments etwf nsafe {A} t mo Q.
(* [comment removed for export] *)
