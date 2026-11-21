(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (38 recorded proofs replaced by written proofs (twfP_mono, twfP_conj, twfP_paths and 35 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Monad MSafe StepB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import Keeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MSafeP () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00c59OSSVerify5KrLib4Spec6MSafeP6nstepPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nstepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StepB7nf_nodeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC59OSSVerify5KrLib3Lib6Decode8errno_ofC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I47Corelib4Init5Logic3and00I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib4Spec5StepB2NFC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K59OSSVerify5KrLib3Lib5Nodes4node01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indK59OSSVerify5KrLib3Lib5Nodes4node02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node08C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node09C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0:C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0;C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0<C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0=C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib7Numbers7BinNums8positive03K59OSSVerify5KrLib3Lib5Nodes4node07C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib3Lib5ITree9itree_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5tpathC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree02C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2ex01C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib4Spec5MSafe3twfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MSafeP4twfPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nsafeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StepB3tnfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MSafeP<nstepP_of_NFC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib3Lib5ITree4bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5MSafe9twf_tsafeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MSafeP=twfP_transferC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5tsafeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indc59OSSVerify5KrLib4Spec6MSafeP5etwfPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5MSafe4etwfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MSafeP8twf_twfPC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00c59OSSVerify5KrLib4Spec6MSafeP9twfP_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MSafeP9twfP_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5ebindC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Keeps4tallC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C59OSSVerify5KrLib4Spec5MSafe;etwf_leavesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITreeDleaves_unreachable_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MSafeP9twfP_conjC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MSafeP:twfP_pathsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4Spec5MSafe4assnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MSafeP:twfP_tpathC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MSafeP:etwf_etwfPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MSafeP:etwfP_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MSafeP;etwfP_ebindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MSafeP:etwfP_tallC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MSafeP6mspecPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5MSafe5mspecC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01c59OSSVerify5KrLib4Spec6MSafeP=mspecP_conseqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4munrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mgetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mputC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00C59OSSVerify5KrLib4Spec5Monad4mupdC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4unit01C59OSSVerify5KrLib4Spec5Monad4msysC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5enodeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib4Spec6MSafeP:mspecP_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mwhenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mloopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MSafeP;mspecP_bindC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3sum00C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindK46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith4Znat5Nat2Z8inj_succI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega:ZMicromega;ZArithProof01C47Corelib4Init5Logic7and_indc59OSSVerify5KrLib4Spec6MSafeP<etwfP_leavesC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition nstepP (n : node) (mo : Model) (rsp : resp) (mo' : Model) (evs : list event) : Prop :=
  nstep n mo rsp mo' evs /\ (nf_node n -> errno_of (eff_ret rsp) = None).

Lemma nstepP_nstep : forall n mo rsp mo' evs, nstepP n mo rsp mo' evs -> nstep n mo rsp mo' evs.
Proof. intros n mo rsp mo' evs [H _]. exact H. Qed.

Lemma nstepP_of_NF : forall n mo rsp mo' evs, NF n mo -> nstep n mo rsp mo' evs -> nstepP n mo rsp mo' evs.
Proof.
  intros n mo rsp mo' evs HN Hst. split; [exact Hst|]. intros Hn.
  destruct n; cbn in Hn; try contradiction; exact (HN _ _ _ Hst).
Qed.

Lemma nstepP_other : forall n mo rsp mo' evs, ~ nf_node n -> nstep n mo rsp mo' evs -> nstepP n mo rsp mo' evs.
Proof. intros n mo rsp mo' evs Hn Hst. split; [exact Hst|]. intros H. exfalso. exact (Hn H). Qed.

Lemma tpath_nstep_of_nstepP : forall {R} (t : itree node R) mo tr r mo',
  tpath nstepP t mo tr r mo' -> tpath nstep t mo tr r mo'.
Proof.
  intros R t. induction t as [x|n k IH]; intros mo tr r mo' Hp; cbn [tpath] in *; [exact Hp|].
  destruct Hp as (rsp & mo1 & evs & tr' & [Hst _] & Hp & ->). exists rsp, mo1, evs, tr'. split; [exact Hst|]. split; [apply IH; exact Hp| reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
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

Lemma twfP_conj : forall {R} (t : itree node R) mo (P1 P2 : R -> Model -> Prop),
  twfP t mo P1 -> twfP t mo P2 -> twfP t mo (fun r mo1 => P1 r mo1 /\ P2 r mo1).
Proof.
  intros R t. induction t as [r|n k IH]; intros mo P1 P2 H1 H2; cbn in *.
  - split; assumption.
  - destruct H1 as [Hs Hk1]. destruct H2 as [_ Hk2]. split; [exact Hs|]. intros rsp mo' evs Hst. apply IH; eauto.
Qed.

(* [comment removed for export] *)
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

Lemma twfP_tsafe : forall {R} (t : itree node R) mo P, twfP t mo P -> tnf t mo -> tsafe nstep nsafe t mo.
Proof. intros R t mo P H HN. eapply twf_tsafe. eapply twfP_transfer; eauto. Qed.

Lemma twfP_tpath : forall {R} (t : itree node R) mo P tr r mo',
  twfP t mo P -> tpath nstepP t mo tr r mo' -> P r mo'.
Proof.
  intros R t. induction t as [r0|n k IH]; intros mo P tr r mo' H Hp; cbn in *.
  - destruct Hp as (<- & -> & ->). exact H.
  - destruct H as [_ Hk]. destruct Hp as (rsp & mo1 & evs & tr' & Hst & Hp & _).
    eapply IH; [eapply Hk; exact Hst| exact Hp].
Qed.

(* [comment removed for export] *)
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

Lemma etwfP_ret : forall {A} (a : A) mo (Q : A -> Model -> Prop), Q a mo -> etwfP (Ret (Ok a)) mo Q.
Proof. intros A a mo Q H. exact H. Qed.

(* [comment removed for export] *)
Lemma etwfP_tall : forall {A} (t : itree node (exc A)) mo (Q : A -> Model -> Prop) (Phi : A -> Prop),
  etwfP t mo Q -> tall Phi t -> etwfP t mo (fun a mo1 => Q a mo1 /\ Phi a).
Proof.
  intros A t. induction t as [r|n k IH]; intros mo Q Phi H Ht; cbn in *.
  - destruct r as [|a]; cbn in *; [exact H| split; [exact H| exact Ht]].
  - destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. apply IH; [eapply Hk; exact Hst| apply Ht].
Qed.

(* [comment removed for export] *)
Lemma etwfP_leaves : forall {A} (t : itree node (exc A)) mo,
  etwfP t mo (fun _ _ => False) -> tnf t mo -> leaves_unreachable_m nstep t mo /\ tsafe nstep nsafe t mo.
Proof.
  intros A t mo H HN. apply etwf_leaves. unfold etwf. eapply twfP_transfer; [exact H| exact HN].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MSpecP.
Context {St : Type}.

Definition mspecP {A} (P : assn St) (m : M St A) (Q : A -> assn St) : Prop :=
  forall s mo, P s mo -> etwfP (m s) mo (fun p mo' => Q (fst p) (snd p) mo').

(* [comment removed for export] *)
Lemma mspec_mspecP {A} (P : assn St) (m : M St A) (Q : A -> assn St) : mspec P m Q -> mspecP P m Q.
Proof. intros H s mo HP. apply etwf_etwfP. exact (H s mo HP). Qed.

Lemma mspecP_ret {A} (a : A) (P : assn St) (Q : A -> assn St) :
  (forall s mo, P s mo -> Q a s mo) -> mspecP P (mret a) Q.
Proof. intros H s mo HP. cbn. apply H. exact HP. Qed.

Lemma mspecP_bind {A B} (m : M St A) (f : A -> M St B) (P : assn St) (Q1 : A -> assn St) (Q : B -> assn St) :
  mspecP P m Q1 -> (forall a, mspecP (Q1 a) (f a) Q) -> mspecP P (mbind m f) Q.
Proof.
  intros Hm Hf s mo HP. unfold mbind. apply etwfP_ebind.
  eapply etwfP_mono; [exact (Hm s mo HP)|]. intros [a s1] mo1 H1. cbn in *. exact (Hf a s1 mo1 H1).
Qed.

Lemma mspecP_conseq {A} (m : M St A) (P P' : assn St) (Q Q' : A -> assn St) :
  mspecP P m Q -> (forall s mo, P' s mo -> P s mo) -> (forall a s mo, Q a s mo -> Q' a s mo) -> mspecP P' m Q'.
Proof.
  intros Hm HP HQ s mo HP'. eapply etwfP_mono; [exact (Hm s mo (HP _ _ HP'))|].
  intros [a s1] mo1; cbn; auto.
Qed.

Lemma mspecP_pre {A} (m : M St A) (P P' : assn St) (Q : A -> assn St) :
  mspecP P m Q -> (forall s mo, P' s mo -> P s mo) -> mspecP P' m Q.
Proof. intros Hm HP. eapply mspecP_conseq; eauto. Qed.

Lemma mspecP_post {A} (m : M St A) (P : assn St) (Q Q' : A -> assn St) :
  mspecP P m Q -> (forall a s mo, Q a s mo -> Q' a s mo) -> mspecP P m Q'.
Proof. intros Hm HQ. eapply mspecP_conseq; eauto. Qed.

Lemma mspecP_munr {A} (Q : A -> assn St) : mspecP (fun _ _ => False) munr Q.
Proof. intros s mo []. Qed.

Lemma mspecP_false {A} (m : M St A) (Q : A -> assn St) : mspecP (fun _ _ => False) m Q.
Proof. intros s mo []. Qed.

Lemma mspecP_get (P : assn St) : mspecP P mget (fun s' s mo => s' = s /\ P s mo).
Proof. intros s mo HP. cbn. auto. Qed.

Lemma mspecP_put (P : assn St) (s1 : St) : mspecP P (mput s1) (fun _ s mo => s = s1 /\ exists s0, P s0 mo).
Proof. intros s mo HP. cbn. eauto. Qed.

Lemma mspecP_upd (P : assn St) (f : St -> St) : mspecP P (mupd f) (fun _ s mo => exists s0, s = f s0 /\ P s0 mo).
Proof. intros s mo HP. cbn. eauto. Qed.

Lemma mspecP_upd' (P : assn St) (Q : unit -> assn St) (f : St -> St) :
  (forall s mo, P s mo -> Q tt (f s) mo) -> mspecP P (mupd f) Q.
Proof. intros H s mo HP. cbn. apply H. exact HP. Qed.

(* [comment removed for export] *)
Lemma mspecP_sys {A} (n : node) (dec : resp -> option A) (P : assn St) (Q : A -> assn St) :
  (forall s mo, P s mo ->
     nsafe n mo /\
     forall rsp mo' evs, nstep n mo rsp mo' evs -> exists a, dec rsp = Some a /\ Q a s mo') ->
  mspecP P (msys n dec) Q.
Proof.
  intros H s mo HP. destruct (H s mo HP) as [Hs Hk]. unfold msys. cbn. split; [exact Hs|].
  intros rsp mo' evs [Hst _]. destruct (Hk rsp mo' evs Hst) as (a & -> & HQ). exact HQ.
Qed.

(* [comment removed for export] *)
Lemma mspecP_sysP {A} (n : node) (dec : resp -> option A) (P : assn St) (Q : A -> assn St) :
  (forall s mo, P s mo ->
     nsafe n mo /\
     forall rsp mo' evs, nstep n mo rsp mo' evs -> (nf_node n -> errno_of (eff_ret rsp) = None) ->
       exists a, dec rsp = Some a /\ Q a s mo') ->
  mspecP P (msys n dec) Q.
Proof.
  intros H s mo HP. destruct (H s mo HP) as [Hs Hk]. unfold msys. cbn. split; [exact Hs|].
  intros rsp mo' evs [Hst HnP]. destruct (Hk rsp mo' evs Hst HnP) as (a & -> & HQ). exact HQ.
Qed.

Lemma mspecP_if {A} (b : bool) (m1 m2 : M St A) (P : assn St) Q :
  (b = true -> mspecP P m1 Q) -> (b = false -> mspecP P m2 Q) -> mspecP P (if b then m1 else m2) Q.
Proof. intros H1 H2. destruct b; auto. Qed.

Lemma mspecP_if_pre {A} (b : bool) (m1 m2 : M St A) (P : assn St) Q :
  mspecP (fun s mo => P s mo /\ b = true) m1 Q -> mspecP (fun s mo => P s mo /\ b = false) m2 Q ->
  mspecP P (if b then m1 else m2) Q.
Proof. intros H1 H2 s mo HP. destruct b; [apply H1|apply H2]; auto. Qed.

Lemma mspecP_exI {A X} (P : X -> assn St) (m : M St A) (Q : A -> assn St) :
  (forall x, mspecP (P x) m Q) -> mspecP (fun s mo => exists x, P x s mo) m Q.
Proof. intros H s mo [x HP]. exact (H x s mo HP). Qed.

Lemma mspecP_pure {A} (P : assn St) (phi : Prop) (m : M St A) (Q : A -> assn St) :
  (phi -> mspecP P m Q) -> mspecP (fun s mo => P s mo /\ phi) m Q.
Proof. intros H s mo [HP Hphi]. exact (H Hphi s mo HP). Qed.

Lemma mspecP_pure_l {A} (P : assn St) (phi : Prop) (m : M St A) (Q : A -> assn St) :
  (phi -> mspecP P m Q) -> mspecP (fun s mo => phi /\ P s mo) m Q.
Proof. intros H s mo [Hphi HP]. exact (H Hphi s mo HP). Qed.

Lemma mspecP_pointwise {A} (P : assn St) (m : M St A) (Q : A -> assn St) :
  (forall s mo, P s mo -> mspecP (fun s' mo' => s' = s /\ mo' = mo) m Q) -> mspecP P m Q.
Proof. intros H s mo HP. apply (H s mo HP). auto. Qed.

Lemma mspecP_when (b : bool) (m : M St unit) (P : assn St) (Q : unit -> assn St) :
  (b = true -> mspecP P m Q) -> (b = false -> forall s mo, P s mo -> Q tt s mo) -> mspecP P (mwhen b m) Q.
Proof. intros H1 H2. unfold mwhen. destruct b; [apply H1; reflexivity|]. apply mspecP_ret. apply H2. reflexivity. Qed.

Lemma mspecP_loop {X R} (body : X -> M St (X + R)) (I : X -> assn St) (Q : R -> assn St) (meas : X -> nat) :
  (forall x, mspecP (I x) (body x)
     (fun r s mo => match r with
                    | inl x' => I x' s mo /\ (meas x' < meas x)%nat
                    | inr v => Q v s mo
                    end)) ->
  forall fuel x, (meas x < fuel)%nat -> mspecP (I x) (mloop fuel body x) Q.
Proof.
  intros Hb fuel. induction fuel as [|fuel IH]; intros x Hf; [lia|].
  cbn [mloop]. eapply mspecP_bind; [apply Hb|].
  intros [x'|v]; cbn.
  - intros s mo [HI Hm]. apply (IH x'); [lia| exact HI].
  - apply mspecP_ret. auto.
Qed.

Lemma mspecP_seq {A B} (m : M St A) (f : A -> M St B) (P R : assn St) (Q : B -> assn St) :
  mspecP P m (fun _ => R) -> (forall a, mspecP R (f a) Q) -> mspecP P (mbind m f) Q.
Proof. intros Hm Hf. eapply mspecP_bind; [exact Hm|]. intros a. apply Hf. Qed.

(* [comment removed for export] *)
Lemma mspecP_conj {A} (P : assn St) (m : M St A) (Q1 Q2 : A -> assn St) :
  mspecP P m Q1 -> mspecP P m Q2 -> mspecP P m (fun a s mo => Q1 a s mo /\ Q2 a s mo).
Proof.
  intros H1 H2 s mo HP. unfold etwfP. eapply twfP_mono; [apply (twfP_conj _ _ _ _ (H1 s mo HP) (H2 s mo HP))|].
  intros [|[a s1]] mo1; cbn; tauto.
Qed.

(* [comment removed for export] *)
Lemma mspecP_paths {A} (P : assn St) (m : M St A) (Q : A -> assn St) (Phi : A -> St -> Prop) :
  mspecP P m Q ->
  (forall s mo tr a s' mo', P s mo -> tpath nstepP (m s) mo tr (Ok (a, s')) mo' -> Phi a s') ->
  mspecP P m (fun a s mo => Q a s mo /\ Phi a s).
Proof.
  intros Hm HPhi s mo HP. unfold etwfP. eapply twfP_paths; [exact (Hm s mo HP)|].
  intros tr [|[a s']] mo' Hp H; cbn in *; [exact H|]. split; [exact H|]. eapply HPhi; [exact HP| exact Hp].
Qed.

(* [comment removed for export] *)
Lemma mspecP_tall {A} (P : assn St) (m : M St A) (Q : A -> assn St) (Phi : A -> St -> Prop) :
  mspecP P m Q -> (forall s, tall (fun p => Phi (fst p) (snd p)) (m s)) -> mspecP P m (fun a s mo => Q a s mo /\ Phi a s).
Proof.
  intros Hm Ht s mo HP. eapply etwfP_mono; [apply (etwfP_tall (m s) mo _ _ (Hm s mo HP) (Ht s))|].
  intros [a s'] mo' [H1 H2]; cbn in *; auto.
Qed.

(* [comment removed for export] *)
Lemma mspecP_tpath {A} : forall (P : assn St) (m : M St A) Q s mo tr a s' mo',
  mspecP P m Q -> P s mo -> tpath nstepP (m s) mo tr (Ok (a, s')) mo' -> Q a s' mo'.
Proof.
  intros P m Q s mo tr a s' mo' Hm HP Hp. pose proof (twfP_tpath _ _ _ _ _ _ (Hm s mo HP) Hp) as H. cbn in H. exact H.
Qed.

(* [comment removed for export] *)
Lemma mspecP_program {A} (P : assn St) (m : M St A) s mo :
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
