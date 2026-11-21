(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (24 recorded proofs replaced by written proofs (etwf_mono, etwf_ebind, etwf_ret and 21 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MSafe () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib4Spec5MSafe3twfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree9itree_indC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nsafeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib3Lib5Nodes5nstepC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C59OSSVerify5KrLib3Lib5ITree4bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5tsafeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib3Lib5ITree5tpathC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2ex00C47Corelib4Init9Datatypes3appc59OSSVerify5KrLib4Spec5MSafe4etwfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5MSafe8twf_monoC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00c59OSSVerify5KrLib4Spec5MSafe8twf_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5ebindC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5enodeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5MSafe9twf_tsafeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5MSafe9twf_tpathC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITreeDleaves_unreachable_mC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5MSafe4assnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5MSafe9etwf_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5MSafe:etwf_ebindC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstc59OSSVerify5KrLib4Spec5MSafe5mspecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01c59OSSVerify5KrLib4Spec5MSafe<mspec_conseqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4munrC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib4Spec5Monad4mgetC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib4Spec5Monad4mputC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00C59OSSVerify5KrLib4Spec5Monad4mupdC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4unit01C59OSSVerify5KrLib4Spec5Monad4msysC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib4Spec5MSafe9mspec_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mwhenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mloopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5MSafe:mspec_bindC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3sum00C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappI47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindK46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith4Znat5Nat2Z8inj_succI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega:ZMicromega;ZArithProof01c59OSSVerify5KrLib4Spec5MSafe;etwf_leavesC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.

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

Lemma etwf_ret : forall {A} (a : A) mo (Q : A -> Model -> Prop), Q a mo -> etwf (Ret (Ok a)) mo Q.
Proof. intros A a mo Q H. exact H. Qed.

Lemma etwf_enode : forall {A} n (pl : resp -> option A) mo (Q : A -> Model -> Prop),
  nsafe n mo ->
  (forall rsp mo' evs, nstep n mo rsp mo' evs -> exists a, pl rsp = Some a /\ Q a mo') ->
  etwf (enode n pl) mo Q.
Proof.
  intros A n pl mo Q Hs Hk. unfold etwf, enode. cbn. split; [exact Hs|].
  intros rsp mo' evs Hst. destruct (Hk rsp mo' evs Hst) as (a & -> & HQ). exact HQ.
Qed.

Lemma etwf_leaves : forall {A} (t : itree node (exc A)) mo,
  etwf t mo (fun _ _ => False) -> leaves_unreachable_m nstep t mo /\ tsafe nstep nsafe t mo.
Proof.
  intros A t mo H. split.
  - intros tr r mo' Hp. pose proof (twf_tpath t mo _ tr r mo' H Hp) as HP. destruct r; exact HP.
  - eapply twf_tsafe. exact H.
Qed.

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

Lemma mspec_post {A} (m : M St A) (P : assn) (Q Q' : A -> assn) :
  mspec P m Q -> (forall a s mo, Q a s mo -> Q' a s mo) -> mspec P m Q'.
Proof. intros Hm HQ. eapply mspec_conseq; eauto. Qed.

Lemma mspec_munr {A} (Q : A -> assn) : mspec (fun _ _ => False) munr Q.
Proof. intros s mo []. Qed.

Lemma mspec_false {A} (m : M St A) (Q : A -> assn) : mspec (fun _ _ => False) m Q.
Proof. intros s mo []. Qed.

Lemma mspec_get (P : assn) : mspec P mget (fun s' s mo => s' = s /\ P s mo).
Proof. intros s mo HP. cbn. auto. Qed.

Lemma mspec_put (P : assn) (s1 : St) : mspec P (mput s1) (fun _ s mo => s = s1 /\ exists s0, P s0 mo).
Proof. intros s mo HP. cbn. eauto. Qed.

Lemma mspec_upd (P : assn) (f : St -> St) : mspec P (mupd f) (fun _ s mo => exists s0, s = f s0 /\ P s0 mo).
Proof. intros s mo HP. cbn. eauto. Qed.

Lemma mspec_upd' (P : assn) (Q : unit -> assn) (f : St -> St) :
  (forall s mo, P s mo -> Q tt (f s) mo) -> mspec P (mupd f) Q.
Proof. intros H s mo HP. cbn. apply H. exact HP. Qed.

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

Lemma mspec_if {A} (b : bool) (m1 m2 : M St A) (P : assn) Q :
  (b = true -> mspec P m1 Q) -> (b = false -> mspec P m2 Q) -> mspec P (if b then m1 else m2) Q.
Proof. intros H1 H2. destruct b; auto. Qed.

(* [comment removed for export] *)
Lemma mspec_if_pre {A} (b : bool) (m1 m2 : M St A) (P : assn) Q :
  mspec (fun s mo => P s mo /\ b = true) m1 Q -> mspec (fun s mo => P s mo /\ b = false) m2 Q ->
  mspec P (if b then m1 else m2) Q.
Proof. intros H1 H2 s mo HP. destruct b; [apply H1|apply H2]; auto. Qed.

(* [comment removed for export] *)
Lemma mspec_exI {A X} (P : X -> assn) (m : M St A) (Q : A -> assn) :
  (forall x, mspec (P x) m Q) -> mspec (fun s mo => exists x, P x s mo) m Q.
Proof. intros H s mo [x HP]. exact (H x s mo HP). Qed.

Lemma mspec_pure {A} (P : assn) (phi : Prop) (m : M St A) (Q : A -> assn) :
  (phi -> mspec P m Q) -> mspec (fun s mo => P s mo /\ phi) m Q.
Proof. intros H s mo [HP Hphi]. exact (H Hphi s mo HP). Qed.

Lemma mspec_pure_l {A} (P : assn) (phi : Prop) (m : M St A) (Q : A -> assn) :
  (phi -> mspec P m Q) -> mspec (fun s mo => phi /\ P s mo) m Q.
Proof. intros H s mo [Hphi HP]. exact (H Hphi s mo HP). Qed.

(* [comment removed for export] *)
Lemma mspec_pointwise {A} (P : assn) (m : M St A) (Q : A -> assn) :
  (forall s mo, P s mo -> mspec (fun s' mo' => s' = s /\ mo' = mo) m Q) -> mspec P m Q.
Proof. intros H s mo HP. apply (H s mo HP). auto. Qed.

(* [comment removed for export] *)
Lemma mspec_when (b : bool) (m : M St unit) (P : assn) (Q : unit -> assn) :
  (b = true -> mspec P m Q) -> (b = false -> forall s mo, P s mo -> Q tt s mo) -> mspec P (mwhen b m) Q.
Proof. intros H1 H2. unfold mwhen. destruct b; [apply H1; reflexivity|]. apply mspec_ret. apply H2. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mspec_loop {X R} (body : X -> M St (X + R)) (I : X -> assn) (Q : R -> assn) (meas : X -> nat) :
  (forall x, mspec (I x) (body x)
     (fun r s mo => match r with
                    | inl x' => I x' s mo /\ (meas x' < meas x)%nat
                    | inr v => Q v s mo
                    end)) ->
  forall fuel x, (meas x < fuel)%nat -> mspec (I x) (mloop fuel body x) Q.
Proof.
  intros Hb fuel. induction fuel as [|fuel IH]; intros x Hf; [lia|].
  cbn [mloop]. eapply mspec_bind; [apply Hb|].
  intros [x'|v]; cbn.
  - intros s mo [HI Hm]. apply (IH x'); [lia| exact HI].
  - apply mspec_ret. auto.
Qed.

(* [comment removed for export] *)
Lemma mspec_seq {A B} (m : M St A) (f : A -> M St B) (P R : assn) (Q : B -> assn) :
  mspec P m (fun _ => R) -> (forall a, mspec R (f a) Q) -> mspec P (mbind m f) Q.
Proof. intros Hm Hf. eapply mspec_bind; [exact Hm|]. intros a. apply Hf. Qed.

(* [comment removed for export] *)
Lemma mspec_program {A} (P : assn) (m : M St A) s mo :
  mspec P m (fun _ _ _ => False) -> P s mo ->
  forall {B} (f : A * St -> itree node (exc B)),
  leaves_unreachable_m nstep (ebind (m s) f) mo /\ tsafe nstep nsafe (ebind (m s) f) mo.
Proof.
  intros Hm HP B f. apply etwf_leaves. apply etwf_ebind.
  eapply etwf_mono; [exact (Hm s mo HP)|]. intros [a s'] mo' [].
Qed.

End MSpec.

Arguments assn St : clear implicits.
Arguments mspec {St A} P m Q.
