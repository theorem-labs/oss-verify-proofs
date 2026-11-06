(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Monad MSafe.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require Import SimW USim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

Section Frame.
Variable I : Model -> Prop.
Hypothesis HI : forall n mo rsp mo' evs, nsafe n mo -> nstep n mo rsp mo' evs -> I mo -> I mo'.

#[using="HI"] Lemma tpath_frame {R} (t : itree node R) : forall mo P tr r mo',
  twf t mo P -> tpath nstep t mo tr r mo' -> I mo -> I mo'.
Proof.
  induction t as [r0|n k IH]; intros mo P tr r mo' HT HP Hi; cbn in HT, HP.
  - destruct HP as (_ & -> & _). exact Hi.
  - destruct HT as [Hs Hk]. destruct HP as (rsp & mo1 & evs & tr' & Hst & Hp & _).
    exact (IH rsp mo1 P tr' r mo' (Hk _ _ _ Hst) Hp (HI _ _ _ _ _ Hs Hst Hi)).
Qed.

Context {StG StC : Type}.
Variable npk : node -> option (machine_state -> resp).
#[local] Notation rel := (@rel StG StC).

(* [comment removed for export] *)
Definition framed (R : rel) : rel := fun sG moG sC moC => R sG moG sC moC /\ I moG.

#[using="HI"] Theorem usim_frame {A B} (R : rel) (mG : M StG A) (mC : M StC B) (Q : A -> B -> rel) :
  usim npk R mG mC Q -> usim npk (framed R) mG mC (fun a b => framed (Q a b)).
Proof.
  intros [HF HS]. split.
  - intros sG moG sC moC [HR Hi]. destruct (HF _ _ _ _ HR) as [HP HE]. split; [| exact HE].
    intros trG a sG' moG' Hp. eapply wreach_mono; [exact (HP _ _ _ _ Hp)|].
    intros tr r mo' (b & sC' & -> & -> & HQ). exists b, sC'. split; [reflexivity|]. split; [reflexivity|]. split; [exact HQ|].
    pose proof (HS _ _ _ _ HR) as HT. unfold etwf in HT. exact (tpath_frame _ _ _ _ _ _ HT Hp Hi).
  - intros sG moG sC moC [HR _]. exact (HS _ _ _ _ HR).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma framed_pre {A B} (R R' : rel) (mG : M StG A) (mC : M StC B) Q :
  usim npk (framed R') mG mC Q -> (forall sG moG sC moC, R sG moG sC moC -> R' sG moG sC moC) -> usim npk (framed R) mG mC Q.
Proof. intros H HR. eapply usim_pre; [exact H|]. intros ? ? ? ? [X Y]. exact (conj (HR _ _ _ _ X) Y). Qed.

#[using="Type"] Lemma framed_exI {A B X} (R : X -> rel) (mG : M StG A) (mC : M StC B) Q :
  (forall x, usim npk (framed (R x)) mG mC Q) -> usim npk (framed (fun sG moG sC moC => exists x, R x sG moG sC moC)) mG mC Q.
Proof.
  intros H. eapply usim_pre; [apply (usim_exI npk (fun x => framed (R x))); exact H|].
  intros ? ? ? ? [[x HR] Hi]. exists x. exact (conj HR Hi).
Qed.

#[using="Type"] Lemma framed_pure {A B} (R : rel) (phi : Prop) (mG : M StG A) (mC : M StC B) Q :
  (phi -> usim npk (framed R) mG mC Q) -> usim npk (framed (fun sG moG sC moC => phi /\ R sG moG sC moC)) mG mC Q.
Proof.
  intros H. eapply usim_pre; [apply (usim_pure npk (framed R) phi); exact H|].
  intros ? ? ? ? [[Hp HR] Hi]. exact (conj Hp (conj HR Hi)).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma framed_use {A B} (R : rel) (mG : M StG A) (mC : M StC B) Q :
  (forall sG moG sC moC, R sG moG sC moC -> I moG -> usim npk (framed R) mG mC Q) -> usim npk (framed R) mG mC Q.
Proof.
  intros H. apply usim_pointwise. intros sG moG sC moC [HR Hi].
  eapply usim_pre; [exact (H _ _ _ _ HR Hi)|]. intros ? ? ? ? (-> & -> & -> & ->). exact (conj HR Hi).
Qed.

End Frame.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ND (p : list byte) (mo : Model) : Prop := fs_under (m_fs mo) p = false.

(* [comment removed for export] *)
Lemma ND_nstep p : forall n mo rsp mo' evs, nsafe n mo -> nstep n mo rsp mo' evs -> ND p mo -> ND p mo'.
Proof. intros n mo rsp mo' evs _ Hst H. unfold ND. rewrite (nstep_fs_under _ _ _ _ _ Hst p). exact H. Qed.

(* [comment removed for export] *)
Definition usim_ND {StG StC A B} p npk (R : @rel StG StC) (mG : M StG A) (mC : M StC B) Q :=
  @usim_frame (ND p) (ND_nstep p) StG StC npk A B R mG mC Q.

