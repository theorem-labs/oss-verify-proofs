(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Monad MSafe StepB.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import Keeps.
Import ListNotations.
Import ITree.Exc.
Definition nstepP (n : node) (mo : Model) (rsp : resp) (mo' : Model) (evs : list event) : Prop :=
nstep n mo rsp mo' evs /\ (nf_node n -> errno_of (eff_ret rsp) = None).
Lemma nstepP_of_NF : forall n mo rsp mo' evs, NF n mo -> nstep n mo rsp mo' evs -> nstepP n mo rsp mo' evs.
Proof.
intros n mo rsp mo' evs HN Hst. split; [exact Hst|]. intros Hn.
destruct n; cbn in Hn; try contradiction; exact (HN _ _ _ Hst).
Qed.
Fixpoint twfP {R} (t : itree node R) (mo : Model) (P : R -> Model -> Prop) : Prop :=
match t with
| Ret r => P r mo
| Vis n k => nsafe n mo /\ forall rsp mo' evs, nstepP n mo rsp mo' evs -> twfP (k rsp) mo' P
end.
Lemma twf_twfP : forall {R} (t : itree node R) mo P, twf t mo P -> twfP t mo P.
Proof.
intros R t. induction t as [r|n k IH]; intros mo P H; cbn in *; [exact H|].
destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs [Hst _]. apply IH. eapply Hk. exact Hst.
Qed.
Lemma twfP_transfer : forall {R} (t : itree node R) mo P, twfP t mo P -> tnf t mo -> twf t mo P.
Proof.
intros R t. induction t as [r|n k IH]; intros mo P H HN; cbn in *; [exact H|].
destruct H as [Hs Hk]. destruct HN as [HNF HNk]. split; [exact Hs|]. intros rsp mo' evs Hst.
apply IH; [| exact (HNk _ _ _ Hst)]. apply (Hk rsp mo' evs). apply nstepP_of_NF; assumption.
Qed.
Lemma twfP_mono : forall {R} (t : itree node R) mo (P P' : R -> Model -> Prop),
twfP t mo P -> (forall r mo1, P r mo1 -> P' r mo1) -> twfP t mo P'.
Proof.
intros R t. induction t as [r|n k IH]; intros mo P P' H HP; cbn in *.
- apply HP. exact H.
- destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. eapply IH; eauto.
Qed.
Lemma twfP_paths : forall {R} (t : itree node R) mo (P P' : R -> Model -> Prop),
twfP t mo P -> (forall tr r mo', tpath nstepP t mo tr r mo' -> P r mo' -> P' r mo') -> twfP t mo P'.
Proof.
intros R t. induction t as [r|n k IH]; intros mo P P' H HP; cbn in *.
- apply (HP [] r mo); [repeat split; reflexivity| exact H].
- destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. eapply IH; [eapply Hk; exact Hst|].
intros tr r mo'' Hp HPr. apply (HP (evs ++ tr) r mo''); [| exact HPr]. exists rsp, mo', evs, tr. auto.
Qed.
Lemma twfP_bind : forall {A B} (t : itree node A) (f : A -> itree node B) mo (P : B -> Model -> Prop),
twfP t mo (fun a mo1 => twfP (f a) mo1 P) -> twfP (ITree.bind node t f) mo P.
Proof.
intros A B t. induction t as [r|n k IH]; intros f mo P H; cbn in *.
- exact H.
- destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. apply IH. eapply Hk; eauto.
Qed.
Definition etwfP {A} (t : itree node (exc A)) (mo : Model) (Q : A -> Model -> Prop) : Prop :=
twfP t mo (fun r mo1 => match r with Unr => False | Ok a => Q a mo1 end).
Lemma etwf_etwfP : forall {A} (t : itree node (exc A)) mo Q, etwf t mo Q -> etwfP t mo Q.
Proof. intros A t mo Q H. apply twf_twfP. exact H. Qed.
Lemma etwfP_mono : forall {A} (t : itree node (exc A)) mo (Q Q' : A -> Model -> Prop),
etwfP t mo Q -> (forall a mo1, Q a mo1 -> Q' a mo1) -> etwfP t mo Q'.
Proof.
intros A t mo Q Q' H HQ. unfold etwfP in *. eapply twfP_mono; [exact H|].
intros [|a] mo1; cbn; auto.
Qed.
Lemma etwfP_ebind : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) mo Q,
etwfP t mo (fun a mo1 => etwfP (f a) mo1 Q) -> etwfP (ebind t f) mo Q.
Proof.
intros A B t f mo Q H. unfold etwfP, ebind in *. apply twfP_bind.
eapply twfP_mono; [exact H|]. intros [|a] mo1 Ha; cbn; [destruct Ha| exact Ha].
Qed.
Lemma etwfP_leaves : forall {A} (t : itree node (exc A)) mo,
etwfP t mo (fun _ _ => False) -> tnf t mo -> leaves_unreachable_m nstep t mo /\ tsafe nstep nsafe t mo.
Proof.
intros A t mo H HN. apply etwf_leaves. unfold etwf. eapply twfP_transfer; [exact H| exact HN].
Qed.
Section MSpecP.
Context {St : Type}.
Definition mspecP {A} (P : assn St) (m : M St A) (Q : A -> assn St) : Prop :=
forall s mo, P s mo -> etwfP (m s) mo (fun p mo' => Q (fst p) (snd p) mo').
#[using="Type"] Lemma mspec_mspecP {A} (P : assn St) (m : M St A) (Q : A -> assn St) : mspec P m Q -> mspecP P m Q.
Proof. intros H s mo HP. apply etwf_etwfP. exact (H s mo HP). Qed.
#[using="Type"] Lemma mspecP_ret {A} (a : A) (P : assn St) (Q : A -> assn St) :
(forall s mo, P s mo -> Q a s mo) -> mspecP P (mret a) Q.
Proof. intros H s mo HP. cbn. apply H. exact HP. Qed.
#[using="Type"] Lemma mspecP_bind {A B} (m : M St A) (f : A -> M St B) (P : assn St) (Q1 : A -> assn St) (Q : B -> assn St) :
mspecP P m Q1 -> (forall a, mspecP (Q1 a) (f a) Q) -> mspecP P (mbind m f) Q.
Proof.
intros Hm Hf s mo HP. unfold mbind. apply etwfP_ebind.
eapply etwfP_mono; [exact (Hm s mo HP)|]. intros [a s1] mo1 H1. cbn in *. exact (Hf a s1 mo1 H1).
Qed.
#[using="Type"] Lemma mspecP_conseq {A} (m : M St A) (P P' : assn St) (Q Q' : A -> assn St) :
mspecP P m Q -> (forall s mo, P' s mo -> P s mo) -> (forall a s mo, Q a s mo -> Q' a s mo) -> mspecP P' m Q'.
Proof.
intros Hm HP HQ s mo HP'. eapply etwfP_mono; [exact (Hm s mo (HP _ _ HP'))|].
intros [a s1] mo1; cbn; auto.
Qed.
#[using="Type"] Lemma mspecP_pre {A} (m : M St A) (P P' : assn St) (Q : A -> assn St) :
mspecP P m Q -> (forall s mo, P' s mo -> P s mo) -> mspecP P' m Q.
Proof. intros Hm HP. eapply mspecP_conseq; eauto. Qed.
#[using="Type"] Lemma mspecP_post {A} (m : M St A) (P : assn St) (Q Q' : A -> assn St) :
mspecP P m Q -> (forall a s mo, Q a s mo -> Q' a s mo) -> mspecP P m Q'.
Proof. intros Hm HQ. eapply mspecP_conseq; eauto. Qed.
#[using="Type"] Lemma mspecP_get (P : assn St) : mspecP P mget (fun s' s mo => s' = s /\ P s mo).
Proof. intros s mo HP. cbn. auto. Qed.
#[using="Type"] Lemma mspecP_upd' (P : assn St) (Q : unit -> assn St) (f : St -> St) :
(forall s mo, P s mo -> Q tt (f s) mo) -> mspecP P (mupd f) Q.
Proof. intros H s mo HP. cbn. apply H. exact HP. Qed.
#[using="Type"] Lemma mspecP_sys {A} (n : node) (dec : resp -> option A) (P : assn St) (Q : A -> assn St) :
(forall s mo, P s mo ->
nsafe n mo /\
forall rsp mo' evs, nstep n mo rsp mo' evs -> exists a, dec rsp = Some a /\ Q a s mo') ->
mspecP P (msys n dec) Q.
Proof.
intros H s mo HP. destruct (H s mo HP) as [Hs Hk]. unfold msys. cbn. split; [exact Hs|].
intros rsp mo' evs [Hst _]. destruct (Hk rsp mo' evs Hst) as (a & -> & HQ). exact HQ.
Qed.
#[using="Type"] Lemma mspecP_if {A} (b : bool) (m1 m2 : M St A) (P : assn St) Q :
(b = true -> mspecP P m1 Q) -> (b = false -> mspecP P m2 Q) -> mspecP P (if b then m1 else m2) Q.
Proof. intros H1 H2. destruct b; auto. Qed.
#[using="Type"] Lemma mspecP_exI {A X} (P : X -> assn St) (m : M St A) (Q : A -> assn St) :
(forall x, mspecP (P x) m Q) -> mspecP (fun s mo => exists x, P x s mo) m Q.
Proof. intros H s mo [x HP]. exact (H x s mo HP). Qed.
#[using="Type"] Lemma mspecP_pure {A} (P : assn St) (phi : Prop) (m : M St A) (Q : A -> assn St) :
(phi -> mspecP P m Q) -> mspecP (fun s mo => P s mo /\ phi) m Q.
Proof. intros H s mo [HP Hphi]. exact (H Hphi s mo HP). Qed.
#[using="Type"] Lemma mspecP_pointwise {A} (P : assn St) (m : M St A) (Q : A -> assn St) :
(forall s mo, P s mo -> mspecP (fun s' mo' => s' = s /\ mo' = mo) m Q) -> mspecP P m Q.
Proof. intros H s mo HP. apply (H s mo HP). auto. Qed.
#[using="Type"] Lemma mspecP_seq {A B} (m : M St A) (f : A -> M St B) (P R : assn St) (Q : B -> assn St) :
mspecP P m (fun _ => R) -> (forall a, mspecP R (f a) Q) -> mspecP P (mbind m f) Q.
Proof. intros Hm Hf. eapply mspecP_bind; [exact Hm|]. intros a. apply Hf. Qed.
#[using="Type"] Lemma mspecP_paths {A} (P : assn St) (m : M St A) (Q : A -> assn St) (Phi : A -> St -> Prop) :
mspecP P m Q ->
(forall s mo tr a s' mo', P s mo -> tpath nstepP (m s) mo tr (Ok (a, s')) mo' -> Phi a s') ->
mspecP P m (fun a s mo => Q a s mo /\ Phi a s).
Proof.
intros Hm HPhi s mo HP. unfold etwfP. eapply twfP_paths; [exact (Hm s mo HP)|].
intros tr [|[a s']] mo' Hp H; cbn in *; [exact H|]. split; [exact H|]. eapply HPhi; [exact HP| exact Hp].
Qed.
#[using="Type"] Lemma mspecP_program {A} (P : assn St) (m : M St A) s mo :
mspecP P m (fun _ _ _ => False) -> P s mo ->
forall {B} (f : A * St -> itree node (exc B)),
tnf (ebind (m s) f) mo ->
leaves_unreachable_m nstep (ebind (m s) f) mo /\ tsafe nstep nsafe (ebind (m s) f) mo.
Proof.
intros Hm HP B f HN. apply etwfP_leaves; [| exact HN]. apply etwfP_ebind.
eapply etwfP_mono; [exact (Hm s mo HP)|]. intros [a s'] mo' [].
Qed.
End MSpecP.
Arguments mspecP {St A} P m Q.
