(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Monad MSafe.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require Import SimW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope mspec_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma twf_of_tpath {R} (t : itree node R) : forall mo (P : R -> Model -> Prop),
  twf t mo (fun _ _ => True) -> (forall tr r mo', tpath nstep t mo tr r mo' -> P r mo') -> twf t mo P.
Proof.
  induction t as [r|n k IH]; intros mo P HT HP; cbn in *.
  - apply (HP []). repeat split; reflexivity.
  - destruct HT as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. apply IH; [exact (Hk _ _ _ Hst)|].
    intros tr r mo'' Hp. apply (HP (evs ++ tr)). exists rsp, mo', evs, tr. auto.
Qed.

Lemma etwf_true_bind {A B} (m : itree node (exc A)) (f : A -> itree node (exc B)) mo :
  etwf m mo (fun _ _ => True) ->
  (forall tr a mo', tpath nstep m mo tr (Ok a) mo' -> etwf (f a) mo' (fun _ _ => True)) ->
  etwf (ebind m f) mo (fun _ _ => True).
Proof.
  intros HT Hf. apply etwf_ebind. unfold etwf in *. apply twf_of_tpath; [eapply twf_mono; [exact HT| intros; exact I]|].
  intros tr [|a] mo' Hp.
  - pose proof (twf_tpath _ _ _ _ _ _ HT Hp) as C. exact C.
  - exact (Hf tr a mo' Hp).
Qed.

Section USim.
Context {StG StC : Type}.
Variable npk : node -> option (machine_state -> resp).
#[local] Notation rel := (@rel StG StC).

(* [comment removed for export] *)
Definition usafe {A} (R : rel) (mG : M StG A) : Prop :=
  forall sG moG sC moC, R sG moG sC moC -> etwf (mG sG) moG (fun _ _ => True).

Definition usim {A B} (R : rel) (mG : M StG A) (mC : M StC B) (Q : A -> B -> rel) : Prop :=
  fsimw npk R mG mC Q /\ usafe R mG.

#[using="Type"] Lemma usim_fsimw {A B} R (mG : M StG A) (mC : M StC B) Q : usim R mG mC Q -> fsimw npk R mG mC Q.
Proof. intros [H _]. exact H. Qed.
#[using="Type"] Lemma usim_usafe {A B} R (mG : M StG A) (mC : M StC B) Q : usim R mG mC Q -> usafe R mG.
Proof. intros [_ H]. exact H. Qed.

#[using="Type"] Lemma usim_of_parts {A B} R (mG : M StG A) (mC : M StC B) Q : fsimw npk R mG mC Q -> usafe R mG -> usim R mG mC Q.
Proof. intros H1 H2. exact (conj H1 H2). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma usim_conseq {A B} (R R' : rel) (mG : M StG A) (mC : M StC B) (Q Q' : A -> B -> rel) :
  usim R' mG mC Q' -> (forall sG moG sC moC, R sG moG sC moC -> R' sG moG sC moC) ->
  (forall a b sG moG sC moC, Q' a b sG moG sC moC -> Q a b sG moG sC moC) -> usim R mG mC Q.
Proof.
  intros [H1 H2] HR HQ. split; [eapply fsimw_conseq; eauto|]. intros sG moG sC moC H. exact (H2 _ _ _ _ (HR _ _ _ _ H)).
Qed.

#[using="Type"] Lemma usim_pre {A B} (R R' : rel) (mG : M StG A) (mC : M StC B) Q :
  usim R' mG mC Q -> (forall sG moG sC moC, R sG moG sC moC -> R' sG moG sC moC) -> usim R mG mC Q.
Proof. intros H HR. eapply usim_conseq; eauto. Qed.

#[using="Type"] Lemma usim_post {A B} (R : rel) (mG : M StG A) (mC : M StC B) (Q Q' : A -> B -> rel) :
  usim R mG mC Q' -> (forall a b sG moG sC moC, Q' a b sG moG sC moC -> Q a b sG moG sC moC) -> usim R mG mC Q.
Proof. intros H HQ. eapply usim_conseq; eauto. Qed.

#[using="Type"] Lemma usim_ret {A B} (R : rel) (a : A) (b : B) (Q : A -> B -> rel) :
  (forall sG moG sC moC, R sG moG sC moC -> Q a b sG moG sC moC) -> usim R (mret a) (mret b) Q.
Proof. intros H. split; [apply fsimw_ret; exact H|]. intros sG moG sC moC _. exact I. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma npeek_inh : (forall n f mo1, npk n = Some f -> exists rsp, nstep n mo1 rsp mo1 []) ->
  forall n f mo1, npk n = Some f -> exists rsp, nstep n mo1 rsp mo1 [].
Proof. auto. Qed.

Hypothesis NPK : forall n f mo1, npk n = Some f -> exists rsp, nstep n mo1 rsp mo1 [].

#[using="NPK"] Lemma usim_bind {A B A' B'} (R : rel) (mG : M StG A) (mC : M StC B) (Q1 : A -> B -> rel)
      (kG : A -> M StG A') (kC : B -> M StC B') (Q : A' -> B' -> rel) :
  usim R mG mC Q1 -> (forall a b, usim (Q1 a b) (kG a) (kC b) Q) -> usim R (mbind mG kG) (mbind mC kC) Q.
Proof.
  intros [H1 S1] H2. split.
  - eapply fsimw_bind; [exact H1|]. intros a b. exact (usim_fsimw _ _ _ _ (H2 a b)).
  - intros sG moG sC moC HR. unfold mbind. apply etwf_true_bind; [exact (S1 _ _ _ _ HR)|].
    intros tr a moG' Hp. destruct a as [a sG'].
    destruct (H1 _ _ _ _ HR) as [HP _]. specialize (HP tr a sG' moG' Hp).
    eapply wreach_tpath in HP; [| exact NPK]. destruct HP as (trC & r & moC' & _ & (b & sC' & -> & _ & HQ)).
    exact (usim_usafe _ _ _ _ (H2 a b) _ _ _ _ HQ).
Qed.

#[using="NPK"] Lemma usim_seq {A B A' B'} (R R1 : rel) (mG : M StG A) (mC : M StC B) (kG : A -> M StG A') (kC : B -> M StC B') (Q : A' -> B' -> rel) :
  usim R mG mC (fun _ _ => R1) -> (forall a b, usim R1 (kG a) (kC b) Q) -> usim R (mbind mG kG) (mbind mC kC) Q.
Proof. intros H1 H2. eapply usim_bind; [exact H1| exact H2]. Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma usim_munr {A B} (R : rel) (mC : M StC B) (Q : A -> B -> rel) :
  (forall sG moG sC moC, R sG moG sC moC -> False) -> usim R (munr (A:=A)) mC Q.
Proof. intros H. split; [apply fsimw_munr|]. intros sG moG sC moC HR. destruct (H _ _ _ _ HR). Qed.

#[using="Type"] Lemma usim_false {A B} (mG : M StG A) (mC : M StC B) (Q : A -> B -> rel) : usim (fun _ _ _ _ => False) mG mC Q.
Proof. split; [apply fsimw_false|]. intros ? ? ? ? []. Qed.

#[using="Type"] Lemma usim_get (R : rel) :
  usim R mget mget (fun a b sG moG sC moC => a = sG /\ b = sC /\ R sG moG sC moC).
Proof. split; [apply fsimw_get|]. intros ? ? ? ? _. exact I. Qed.

#[using="Type"] Lemma usim_upd (R : rel) (Q : unit -> unit -> rel) (fG : StG -> StG) (fC : StC -> StC) :
  (forall sG moG sC moC, R sG moG sC moC -> Q tt tt (fG sG) moG (fC sC) moC) -> usim R (mupd fG) (mupd fC) Q.
Proof. intros H. split; [apply fsimw_upd; exact H|]. intros ? ? ? ? _. exact I. Qed.

#[using="Type"] Lemma usim_pure {A B} (R : rel) (phi : Prop) (mG : M StG A) (mC : M StC B) Q :
  (phi -> usim R mG mC Q) -> usim (fun sG moG sC moC => phi /\ R sG moG sC moC) mG mC Q.
Proof. intros H. split; [apply fsimw_pure; intros Hp; exact (usim_fsimw _ _ _ _ (H Hp))|]. intros ? ? ? ? [Hp HR]. exact (usim_usafe _ _ _ _ (H Hp) _ _ _ _ HR). Qed.

#[using="Type"] Lemma usim_exI {A B X} (R : X -> rel) (mG : M StG A) (mC : M StC B) Q :
  (forall x, usim (R x) mG mC Q) -> usim (fun sG moG sC moC => exists x, R x sG moG sC moC) mG mC Q.
Proof. intros H. split; [apply fsimw_exI; intros x; exact (usim_fsimw _ _ _ _ (H x))|]. intros ? ? ? ? [x HR]. exact (usim_usafe _ _ _ _ (H x) _ _ _ _ HR). Qed.

#[using="Type"] Lemma usim_pointwise {A B} (R : rel) (mG : M StG A) (mC : M StC B) Q :
  (forall sG moG sC moC, R sG moG sC moC ->
     usim (fun sG' moG' sC' moC' => sG' = sG /\ moG' = moG /\ sC' = sC /\ moC' = moC) mG mC Q) ->
  usim R mG mC Q.
Proof.
  intros H. split; [apply fsimw_pointwise; intros; exact (usim_fsimw _ _ _ _ (H _ _ _ _ H0))|].
  intros ? ? ? ? HR. exact (usim_usafe _ _ _ _ (H _ _ _ _ HR) _ _ _ _ (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))).
Qed.

#[using="NPK"] Lemma usim_bind_eq {A A' B'} (R : rel) (mG : M StG A) (mC : M StC A) (R1 : A -> rel)
      (kG : A -> M StG A') (kC : A -> M StC B') (Q : A' -> B' -> rel) :
  usim R mG mC (fun a b sG moG sC moC => a = b /\ R1 a sG moG sC moC) ->
  (forall a, usim (R1 a) (kG a) (kC a) Q) -> usim R (mbind mG kG) (mbind mC kC) Q.
Proof.
  intros H1 H2. eapply usim_bind; [exact H1|]. intros a b. apply usim_pure. intros <-. apply H2.
Qed.

(* [comment removed for export] *)
#[using="NPK"] Lemma usim_loopV {X Y A B} (I : X -> Y -> rel) (V : X -> nat -> Prop) (Q : A -> B -> rel)
      (bodyG : X -> M StG (X + A)) (bodyC : Y -> M StC (Y + B)) :
  (forall x y n, V x (S n) -> usim (I x y) (bodyG x) (bodyC y)
     (fun r r' sG moG sC moC => match r, r' with
                                | inl x', inl y' => V x' n /\ I x' y' sG moG sC moC
                                | inr a, inr b => Q a b sG moG sC moC
                                | _, _ => False
                                end)) ->
  (forall x, V x 0%nat -> False) ->
  forall fuel x y, V x fuel -> usim (I x y) (mloop fuel bodyG x) (mloop fuel bodyC y) Q.
Proof.
  intros Hb HV0 fuel. induction fuel as [|fuel IH]; intros x y HV; cbn [mloop].
  - destruct (HV0 x HV).
  - eapply usim_bind; [apply (Hb x y fuel HV)|]. intros [x'|a] [y'|b]; cbn beta.
    + apply usim_pure. intros HV'. apply IH. exact HV'.
    + apply usim_false.
    + apply usim_false.
    + apply usim_ret. auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma usim_sys {A B} (nG nC : node) (decG : resp -> option A) (decC : resp -> option B) (R : rel) (Q : A -> B -> rel) :
  npk nC = None ->
  (forall sG moG sC moC, R sG moG sC moC ->
     nsafe nG moG
     /\ (forall rspG moG' evs, nstep nG moG rspG moG' evs -> exists a, decG rspG = Some a)
     /\ (forall rspG moG' evs a, nstep nG moG rspG moG' evs -> decG rspG = Some a ->
        exists rspC moC' b, nstep nC moC rspC moC' evs /\ decC rspC = Some b /\ Q a b sG moG' sC moC')
     /\ (forall code moG', nexit nG moG code moG' ->
        exists moC', nexit nC moC code moC' /\ m_fs moC' = m_fs moG')) ->
  usim R (msys nG decG) (msys nC decC) Q.
Proof.
  intros Hnp H. split.
  - apply fsimw_sys; [exact Hnp|]. intros sG moG sC moC HR. destruct (H _ _ _ _ HR) as (_ & _ & HS & HX). auto.
  - intros sG moG sC moC HR. destruct (H _ _ _ _ HR) as (Hs & Hd & _ & _).
    unfold msys. apply etwf_enode; [exact Hs|]. intros rsp mo' evs Hst. destruct (Hd _ _ _ Hst) as [a Ha].
    exists (a, sG). rewrite Ha. split; [reflexivity| exact I].
Qed.

End USim.

Arguments usim {StG StC} npk {A B} R mG mC Q.

