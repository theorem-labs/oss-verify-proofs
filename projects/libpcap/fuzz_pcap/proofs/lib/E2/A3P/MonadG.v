(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg AProto.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section ImplMG.
  Context {St : Type}.
  Local Notation M := (Monad.M St).

  Definition implMG {A} (RNG : footprint) (c : M A) (s : St)
      (Q : A -> St -> footprint -> machine_state -> Prop) (ms : machine_state) : Prop :=
    implS asegs RNG (c s) (epostF (fun p => Q (fst p) (snd p))) ms.

  #[using="Type"] Lemma implMG_fold : forall {A} RNG (c : M A) s Q ms,
    implS asegs RNG (c s) (epostF (fun p => Q (fst p) (snd p))) ms -> implMG RNG c s Q ms.
  Proof. intros. exact H. Qed.
  #[using="Type"] Lemma implMG_unfold : forall {A} RNG (c : M A) s Q ms,
    implMG RNG c s Q ms -> implS asegs RNG (c s) (epostF (fun p => Q (fst p) (snd p))) ms.
  Proof. intros. exact H. Qed.

  #[using="Type"] Lemma implMG_ret : forall {A} RNG (a : A) (s : St) (Q : A -> St -> footprint -> machine_state -> Prop) ms,
    evtF asegs RNG (Q a s RNG) ms -> implMG RNG (mret a) s Q ms.
  Proof. intros A RNG a s Q ms H. unfold implMG, mret. apply implF_ret_ok. exact H. Qed.

  #[using="Type"] Lemma implMG_unr : forall {A} RNG (s : St) (Q : A -> St -> footprint -> machine_state -> Prop) ms,
    implMG RNG (munr (A:=A)) s Q ms.
  Proof. intros. unfold implMG, munr. apply implF_ret_unr. Qed.

  #[using="Type"] Lemma implMG_bind : forall {A B} RNG (ma : M A) (f : A -> M B) (s : St)
      (Q1 : A -> St -> footprint -> machine_state -> Prop) (Q : B -> St -> footprint -> machine_state -> Prop) ms,
    implMG RNG ma s Q1 ms ->
    (forall a s' RNG' ms', Q1 a s' RNG' ms' -> implMG RNG' (f a) s' Q ms') ->
    implMG RNG (mbind ma f) s Q ms.
  Proof.
    intros A B RNG ma f s Q1 Q ms Hm Hf. unfold implMG, mbind in *.
    eapply implF_ebind; [exact Hm|]. intros [a s'] RNG' ms' H. cbn in *. apply Hf. exact H.
  Qed.

  #[using="Type"] Lemma implMG_mono : forall {A} RNG (ma : M A) (s : St) (Q Q' : A -> St -> footprint -> machine_state -> Prop) ms,
    implMG RNG ma s Q ms -> (forall a s' RNG' ms', Q a s' RNG' ms' -> Q' a s' RNG' ms') -> implMG RNG ma s Q' ms.
  Proof.
    intros A RNG ma s Q Q' ms H HQ. unfold implMG in *. eapply implF_epost_mono; [exact H|]. intros [a s'] RNG' ms'; cbn; auto.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma implMG_evtF : forall {A} RNG (ma : M A) (s : St) (Q : A -> St -> footprint -> machine_state -> Prop) P ms,
    evtF asegs RNG P ms -> (forall ms', P ms' -> implMG RNG ma s Q ms') -> implMG RNG ma s Q ms.
  Proof. intros A RNG ma s Q P ms H K. unfold implMG in *. eapply implF_evtF; eauto. Qed.

  #[using="Type"] Lemma implMG_from_evtF : forall {A} RNG (ma : M A) (s : St) (Q : A -> St -> footprint -> machine_state -> Prop) ms,
    evtF asegs RNG (fun ms' => implMG RNG ma s Q ms') ms -> implMG RNG ma s Q ms.
  Proof. intros A RNG ma s Q ms H. eapply implMG_evtF; [exact H|]. cbv beta. intros ms' H'; exact H'. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma implMG_post_evtF : forall {A} RNG (ma : M A) (s : St) (Q Q' : A -> St -> footprint -> machine_state -> Prop) ms,
    implMG RNG ma s Q' ms ->
    (forall a s' RNG' ms', Q' a s' RNG' ms' -> evtF asegs RNG' (Q a s' RNG') ms') ->
    implMG RNG ma s Q ms.
  Proof.
    intros A RNG ma s Q Q' ms H HQ. unfold implMG in *. eapply implF_epost_evtF; [exact H|]. intros [a s'] RNG' ms'; cbn; auto.
  Qed.

  #[using="Type"] Lemma implMG_get : forall RNG (s : St) (Q : St -> St -> footprint -> machine_state -> Prop) ms,
    evtF asegs RNG (Q s s RNG) ms -> implMG RNG mget s Q ms.
  Proof. intros. unfold implMG, mget. apply implF_ret_ok. exact H. Qed.
  #[using="Type"] Lemma implMG_upd : forall RNG f (s : St) (Q : unit -> St -> footprint -> machine_state -> Prop) ms,
    evtF asegs RNG (Q tt (f s) RNG) ms -> implMG RNG (mupd f) s Q ms.
  Proof. intros. unfold implMG, mupd. apply implF_ret_ok. exact H. Qed.
End ImplMG.
End CANSEC1.
Arguments implMG {St A} RNG c s Q ms.

(* [comment removed for export] *)
Ltac ienterG := lazymatch goal with |- implMG _ _ _ _ _ => apply implMG_from_evtF | _ => idtac end.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Fpu LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section ImplMG.
  Context {St : Type}.
  Local Notation M := (Monad.M St).

  Definition implMG {A} (RNG : footprint) (c : M A) (s : St)
      (Q : A -> St -> footprint -> machine_state -> Prop) (ms : machine_state) : Prop :=
    implS asegs RNG (c s) (epostF (fun p => Q (fst p) (snd p))) ms.

  #[using="Type"] Lemma implMG_fold : forall {A} RNG (c : M A) s Q ms,
    implS asegs RNG (c s) (epostF (fun p => Q (fst p) (snd p))) ms -> implMG RNG c s Q ms.
  Proof. intros. exact H. Qed.
  #[using="Type"] Lemma implMG_unfold : forall {A} RNG (c : M A) s Q ms,
    implMG RNG c s Q ms -> implS asegs RNG (c s) (epostF (fun p => Q (fst p) (snd p))) ms.
  Proof. intros. exact H. Qed.

  #[using="Type"] Lemma implMG_ret : forall {A} RNG (a : A) (s : St) (Q : A -> St -> footprint -> machine_state -> Prop) ms,
    evtF asegs RNG (Q a s RNG) ms -> implMG RNG (mret a) s Q ms.
  Proof. intros A RNG a s Q ms H. unfold implMG, mret. apply implF_ret_ok. exact H. Qed.

  #[using="Type"] Lemma implMG_unr : forall {A} RNG (s : St) (Q : A -> St -> footprint -> machine_state -> Prop) ms,
    implMG RNG (munr (A:=A)) s Q ms.
  Proof. intros. unfold implMG, munr. apply implF_ret_unr. Qed.

  #[using="Type"] Lemma implMG_bind : forall {A B} RNG (ma : M A) (f : A -> M B) (s : St)
      (Q1 : A -> St -> footprint -> machine_state -> Prop) (Q : B -> St -> footprint -> machine_state -> Prop) ms,
    implMG RNG ma s Q1 ms ->
    (forall a s' RNG' ms', Q1 a s' RNG' ms' -> implMG RNG' (f a) s' Q ms') ->
    implMG RNG (mbind ma f) s Q ms.
  Proof.
    intros A B RNG ma f s Q1 Q ms Hm Hf. unfold implMG, mbind in *.
    eapply implF_ebind; [exact Hm|]. intros [a s'] RNG' ms' H. cbn in *. apply Hf. exact H.
  Qed.

  #[using="Type"] Lemma implMG_mono : forall {A} RNG (ma : M A) (s : St) (Q Q' : A -> St -> footprint -> machine_state -> Prop) ms,
    implMG RNG ma s Q ms -> (forall a s' RNG' ms', Q a s' RNG' ms' -> Q' a s' RNG' ms') -> implMG RNG ma s Q' ms.
  Proof.
    intros A RNG ma s Q Q' ms H HQ. unfold implMG in *. eapply implF_epost_mono; [exact H|]. intros [a s'] RNG' ms'; cbn; auto.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma implMG_evtF : forall {A} RNG (ma : M A) (s : St) (Q : A -> St -> footprint -> machine_state -> Prop) P ms,
    evtF asegs RNG P ms -> (forall ms', P ms' -> implMG RNG ma s Q ms') -> implMG RNG ma s Q ms.
  Proof. intros A RNG ma s Q P ms H K. unfold implMG in *. eapply implF_evtF; eauto. Qed.

  #[using="Type"] Lemma implMG_from_evtF : forall {A} RNG (ma : M A) (s : St) (Q : A -> St -> footprint -> machine_state -> Prop) ms,
    evtF asegs RNG (fun ms' => implMG RNG ma s Q ms') ms -> implMG RNG ma s Q ms.
  Proof. intros A RNG ma s Q ms H. eapply implMG_evtF; [exact H|]. cbv beta. intros ms' H'; exact H'. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma implMG_post_evtF : forall {A} RNG (ma : M A) (s : St) (Q Q' : A -> St -> footprint -> machine_state -> Prop) ms,
    implMG RNG ma s Q' ms ->
    (forall a s' RNG' ms', Q' a s' RNG' ms' -> evtF asegs RNG' (Q a s' RNG') ms') ->
    implMG RNG ma s Q ms.
  Proof.
    intros A RNG ma s Q Q' ms H HQ. unfold implMG in *. eapply implF_epost_evtF; [exact H|]. intros [a s'] RNG' ms'; cbn; auto.
  Qed.

  #[using="Type"] Lemma implMG_get : forall RNG (s : St) (Q : St -> St -> footprint -> machine_state -> Prop) ms,
    evtF asegs RNG (Q s s RNG) ms -> implMG RNG mget s Q ms.
  Proof. intros. unfold implMG, mget. apply implF_ret_ok. exact H. Qed.
  #[using="Type"] Lemma implMG_upd : forall RNG f (s : St) (Q : unit -> St -> footprint -> machine_state -> Prop) ms,
    evtF asegs RNG (Q tt (f s) RNG) ms -> implMG RNG (mupd f) s Q ms.
  Proof. intros. unfold implMG, mupd. apply implF_ret_ok. exact H. Qed.
End ImplMG.
End CANSEC1.
Arguments implMG {St A} RNG c s Q ms.

(* [comment removed for export] *)
Ltac ienterG := lazymatch goal with |- implMG _ _ _ _ _ => apply implMG_from_evtF | _ => idtac end.
End TwB.
