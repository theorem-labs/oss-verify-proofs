(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Monad MSafe.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

Definition okR (n : node) (rsp : resp) : Prop :=
  match n with
  | NMmap _ _ _ flags => Z.land flags Prog.MAP_FIXED_Z = 0%Z -> errno_of (eff_ret rsp) = None
  | NMprotect _ _ _ => errno_of (eff_ret rsp) = None
  | _ => True
  end.

Definition nstepR (n : node) (mo : Model) (rsp : resp) (mo' : Model) (evs : list event) : Prop :=
  nstep n mo rsp mo' evs /\ okR n rsp.

Definition no_enomemR (n : node) (mo : Model) : Prop :=
  match n with
  | NMmap _ _ _ flags => Z.land flags Prog.MAP_FIXED_Z = 0%Z ->
      forall rsp mo' evs, nstep n mo rsp mo' evs -> errno_of (eff_ret rsp) = None
  | NMprotect _ _ _ => forall rsp mo' evs, nstep n mo rsp mo' evs -> errno_of (eff_ret rsp) = None
  | _ => True
  end.

Lemma no_enomemR_okR : forall n mo rsp mo' evs, no_enomemR n mo -> nstep n mo rsp mo' evs -> okR n rsp.
Proof.
  intros n mo rsp mo' evs Hn Hst. destruct n; cbn in *; try exact I.
  - intros Hf. exact (Hn Hf rsp mo' evs Hst).
  - exact (Hn rsp mo' evs Hst).
Qed.

Fixpoint twfR {R} (t : itree node R) (mo : Model) (P : R -> Model -> Prop) : Prop :=
  match t with
  | Ret r => P r mo
  | Vis n k => nsafe n mo /\ forall rsp mo' evs, nstepR n mo rsp mo' evs -> twfR (k rsp) mo' P
  end.

Lemma twfR_mono : forall {R} (t : itree node R) mo (P P' : R -> Model -> Prop),
  twfR t mo P -> (forall r mo1, P r mo1 -> P' r mo1) -> twfR t mo P'.
Proof.
  intros R t. induction t as [r|n k IH]; intros mo P P' H HP; cbn in *.
  - apply HP. exact H.
  - destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. eapply IH; eauto.
Qed.

Lemma twfR_bind : forall {A B} (t : itree node A) (f : A -> itree node B) mo (P : B -> Model -> Prop),
  twfR t mo (fun a mo1 => twfR (f a) mo1 P) -> twfR (ITree.bind node t f) mo P.
Proof.
  intros A B t. induction t as [r|n k IH]; intros f mo P H; cbn in *.
  - exact H.
  - destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. apply IH. eapply Hk; eauto.
Qed.

Definition etwfR {A} (t : itree node (exc A)) (mo : Model) (Q : A -> Model -> Prop) : Prop :=
  twfR t mo (fun r mo1 => match r with Unr => False | Ok a => Q a mo1 end).

Lemma etwfR_mono : forall {A} (t : itree node (exc A)) mo (Q Q' : A -> Model -> Prop),
  etwfR t mo Q -> (forall a mo1, Q a mo1 -> Q' a mo1) -> etwfR t mo Q'.
Proof.
  intros A t mo Q Q' H HQ. unfold etwfR in *. eapply twfR_mono; [exact H|].
  intros [|a] mo1; cbn; auto.
Qed.

Lemma etwfR_ebind : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) mo Q,
  etwfR t mo (fun a mo1 => etwfR (f a) mo1 Q) -> etwfR (ebind t f) mo Q.
Proof.
  intros A B t f mo Q H. unfold etwf, ebind in *. apply twfR_bind.
  eapply twfR_mono; [exact H|]. intros [|a] mo1 Ha; cbn; [destruct Ha| exact Ha].
Qed.

Section MSpec.
Context {St : Type}.

Definition assn : Type := St -> Model -> Prop.

Definition mspecR {A} (P : assn) (m : M St A) (Q : A -> assn) : Prop :=
  forall s mo, P s mo -> etwfR (m s) mo (fun p mo' => Q (fst p) (snd p) mo').

Lemma mspecR_ret {A} (a : A) (P : assn) (Q : A -> assn) :
  (forall s mo, P s mo -> Q a s mo) -> mspecR P (mret a) Q.
Proof. intros H s mo HP. cbn. apply H. exact HP. Qed.

Lemma mspecR_bind {A B} (m : M St A) (f : A -> M St B) (P : assn) (Q1 : A -> assn) (Q : B -> assn) :
  mspecR P m Q1 -> (forall a, mspecR (Q1 a) (f a) Q) -> mspecR P (mbind m f) Q.
Proof.
  intros Hm Hf s mo HP. unfold mbind. apply etwfR_ebind.
  eapply etwfR_mono; [exact (Hm s mo HP)|]. intros [a s1] mo1 H1. cbn in *. exact (Hf a s1 mo1 H1).
Qed.

Lemma mspecR_conseq {A} (m : M St A) (P P' : assn) (Q Q' : A -> assn) :
  mspecR P m Q -> (forall s mo, P' s mo -> P s mo) -> (forall a s mo, Q a s mo -> Q' a s mo) -> mspecR P' m Q'.
Proof.
  intros Hm HP HQ s mo HP'. eapply etwfR_mono; [exact (Hm s mo (HP _ _ HP'))|].
  intros [a s1] mo1; cbn; auto.
Qed.

Lemma mspecR_pre {A} (m : M St A) (P P' : assn) (Q : A -> assn) :
  mspecR P m Q -> (forall s mo, P' s mo -> P s mo) -> mspecR P' m Q.
Proof. intros Hm HP. eapply mspecR_conseq; eauto. Qed.

Lemma mspecR_post {A} (m : M St A) (P : assn) (Q Q' : A -> assn) :
  mspecR P m Q -> (forall a s mo, Q a s mo -> Q' a s mo) -> mspecR P m Q'.
Proof. intros Hm HQ. eapply mspecR_conseq; eauto. Qed.

Lemma mspecR_munr {A} (Q : A -> assn) : mspecR (fun _ _ => False) munr Q.
Proof. intros s mo []. Qed.

Lemma mspecR_get (P : assn) : mspecR P mget (fun s' s mo => s' = s /\ P s mo).
Proof. intros s mo HP. cbn. auto. Qed.

Lemma mspecR_sys {A} (n : node) (dec : resp -> option A) (P : assn) (Q : A -> assn) :
  (forall s mo, P s mo ->
     nsafe n mo /\
     forall rsp mo' evs, nstepR n mo rsp mo' evs -> exists a, dec rsp = Some a /\ Q a s mo') ->
  mspecR P (msys n dec) Q.
Proof.
  intros H s mo HP. destruct (H s mo HP) as [Hs Hk]. unfold msys. cbn. split; [exact Hs|].
  intros rsp mo' evs Hst. destruct (Hk rsp mo' evs Hst) as (a & -> & HQ). exact HQ.
Qed.

Lemma mspecR_if {A} (b : bool) (m1 m2 : M St A) (P : assn) Q :
  (b = true -> mspecR P m1 Q) -> (b = false -> mspecR P m2 Q) -> mspecR P (if b then m1 else m2) Q.
Proof. intros H1 H2. destruct b; auto. Qed.

Lemma mspecR_if_pre {A} (b : bool) (m1 m2 : M St A) (P : assn) Q :
  mspecR (fun s mo => P s mo /\ b = true) m1 Q -> mspecR (fun s mo => P s mo /\ b = false) m2 Q ->
  mspecR P (if b then m1 else m2) Q.
Proof. intros H1 H2 s mo HP. destruct b; [apply H1|apply H2]; auto. Qed.

Lemma mspecR_exI {A X} (P : X -> assn) (m : M St A) (Q : A -> assn) :
  (forall x, mspecR (P x) m Q) -> mspecR (fun s mo => exists x, P x s mo) m Q.
Proof. intros H s mo [x HP]. exact (H x s mo HP). Qed.

Lemma mspecR_pure {A} (P : assn) (phi : Prop) (m : M St A) (Q : A -> assn) :
  (phi -> mspecR P m Q) -> mspecR (fun s mo => P s mo /\ phi) m Q.
Proof. intros H s mo [HP Hphi]. exact (H Hphi s mo HP). Qed.

Lemma mspecR_pointwise {A} (P : assn) (m : M St A) (Q : A -> assn) :
  (forall s mo, P s mo -> mspecR (fun s' mo' => s' = s /\ mo' = mo) m Q) -> mspecR P m Q.
Proof. intros H s mo HP. apply (H s mo HP). auto. Qed.

Lemma mspecR_loop {X R} (body : X -> M St (X + R)) (I : X -> assn) (Q : R -> assn) (meas : X -> nat) :
  (forall x, mspecR (I x) (body x)
     (fun r s mo => match r with
                    | inl x' => I x' s mo /\ (meas x' < meas x)%nat
                    | inr v => Q v s mo
                    end)) ->
  forall fuel x, (meas x < fuel)%nat -> mspecR (I x) (mloop fuel body x) Q.
Proof.
  intros Hb fuel. induction fuel as [|fuel IH]; intros x Hf; [lia|].
  cbn [mloop]. eapply mspecR_bind; [apply Hb|].
  intros [x'|v]; cbn.
  - intros s mo [HI Hm]. apply (IH x'); [lia| exact HI].
  - apply mspecR_ret. auto.
Qed.

Lemma mspecR_seq {A B} (m : M St A) (f : A -> M St B) (P R : assn) (Q : B -> assn) :
  mspecR P m (fun _ => R) -> (forall a, mspecR R (f a) Q) -> mspecR P (mbind m f) Q.
Proof. intros Hm Hf. eapply mspecR_bind; [exact Hm|]. intros a. apply Hf. Qed.

End MSpec.

Arguments assn St : clear implicits.
Arguments mspecR {St A} P m Q.

Lemma twf_twfR : forall {R} (t : itree node R) mo P, twf t mo P -> twfR t mo P.
Proof.
  intros R t. induction t as [r|n k IH]; intros mo P H; cbn in *; [exact H|].
  destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs [Hst _]. apply IH. eapply Hk. exact Hst.
Qed.

Lemma etwf_etwfR : forall {A} (t : itree node (exc A)) mo Q, etwf t mo Q -> etwfR t mo Q.
Proof. intros A t mo Q H. unfold etwf, etwfR in *. apply twf_twfR. exact H. Qed.

Lemma mspec_mspecR : forall {St A} (P : assn St) (m : M St A) (Q : A -> assn St), mspec P m Q -> mspecR P m Q.
Proof. intros St A P m Q H s mo HP. apply etwf_etwfR. exact (H s mo HP). Qed.

Lemma twfR_twf : forall {R} (t : itree node R) mo P, tsafe nstep no_enomemR t mo -> twfR t mo P -> twf t mo P.
Proof.
  intros R t. induction t as [r|n k IH]; intros mo P Hs H; cbn in *; [exact H|].
  destruct H as [Hn Hk]. destruct Hs as [Hne Hsk]. split; [exact Hn|].
  intros rsp mo' evs Hst. apply IH; [eapply Hsk; exact Hst|]. apply (Hk rsp mo' evs). split; [exact Hst|]. eapply no_enomemR_okR; [exact Hne | exact Hst].
Qed.

Lemma etwfR_leaves_nstep : forall {A} (t : itree node (exc A)) mo,
  tsafe nstep no_enomemR t mo -> etwfR t mo (fun _ _ => False) -> leaves_unreachable_m nstep t mo /\ tsafe nstep nsafe t mo.
Proof. intros A t mo Hs H. apply etwf_leaves. unfold etwf. apply twfR_twf; [exact Hs | exact H]. Qed.

Lemma mspecR_program_nstep {St A} (P : assn St) (m : M St A) s mo :
  mspecR P m (fun _ _ _ => False) -> P s mo ->
  forall {B} (f : A * St -> itree node (exc B)),
  tsafe nstep no_enomemR (ebind (m s) f) mo ->
  leaves_unreachable_m nstep (ebind (m s) f) mo /\ tsafe nstep nsafe (ebind (m s) f) mo.
Proof.
  intros Hm HP B f Hs. apply etwfR_leaves_nstep; [exact Hs|]. apply etwfR_ebind.
  eapply etwfR_mono; [exact (Hm s mo HP)|]. intros [a s'] mo' [].
Qed.
