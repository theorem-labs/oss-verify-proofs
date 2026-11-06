(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_mlib__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_mlib.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto MonadF. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_kit__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_kit__A3W.MonadF2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section ImplXM.
  Variable atn : node -> footprint -> machine_state -> Prop.
  Variable sil_ : footprint -> machine_state -> machine_state -> Prop.
  Variable npk_ : node -> option (machine_state -> resp).
  Variable fst_ : node -> resp -> footprint -> footprint -> Prop.
  Context {St : Type}.
  Local Notation M := (Monad.M St).
  Local Open Scope mspec_scope.
  Local Notation implF := (@ITreeA.implF node asegs atn sil_ npk_ fst_ _).

  Definition implXM {A} (RNG : footprint) (c : M A) (s : St) (Q : A -> St -> machine_state -> Prop) (ms : machine_state) : Prop :=
    implF RNG (c s) (epostF (postF RNG Q)) ms.

  #[using="Type"] Lemma implXM_ret : forall {A} RNG (a : A) s Q ms, evtF asegs RNG (Q a s) ms -> implXM RNG (mret a) s Q ms.
  Proof. intros A RNG a s Q ms H. unfold implXM, mret. apply implF_ret_ok. cbn. eapply evtF_mono; [exact H|]. intros; split; auto. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma implXM_retF : forall {A} RNG (Q : A -> St -> machine_state -> Prop) (p : A * St) ms,
    evtF asegs RNG (Q (fst p) (snd p)) ms -> implF RNG (Ret (Ok p)) (epostF (postF RNG Q)) ms.
  Proof. intros A RNG Q [a s] ms H. apply implF_ret_ok. cbn. eapply evtF_mono; [exact H|]. intros; split; auto. Qed.

  #[using="Type"] Lemma implXM_unr : forall {A} RNG s (Q : A -> St -> machine_state -> Prop) ms, implXM RNG munr s Q ms.
  Proof. intros. unfold implXM, munr. apply implF_ret_unr. Qed.

  #[using="Type"] Lemma implXM_bind : forall {A B} RNG (m : M A) (f : A -> M B) s Q1 Q ms,
    implXM RNG m s Q1 ms ->
    (forall a s' ms', Q1 a s' ms' -> implXM RNG (f a) s' Q ms') ->
    implXM RNG (mbind m f) s Q ms.
  Proof.
    intros A B RNG m f s Q1 Q ms Hm Hf. unfold implXM, mbind in *.
    eapply implF_ebind; [exact Hm|]. intros [a s'] RNG' ms' [-> H]. cbn in *. apply Hf. exact H.
  Qed.

  #[using="Type"] Lemma implXM_mono : forall {A} RNG (m : M A) s (Q Q' : A -> St -> machine_state -> Prop) ms,
    implXM RNG m s Q ms -> (forall a s' ms', Q a s' ms' -> Q' a s' ms') -> implXM RNG m s Q' ms.
  Proof.
    intros A RNG m s Q Q' ms H HQ. unfold implXM in *. eapply implF_epost_mono; [exact H|].
    intros [a s'] RNG' ms' [E H']; split; [exact E| apply HQ; exact H'].
  Qed.

  #[using="Type"] Lemma implXM_eq_ms : forall {X} RNG (c : M X) s Q ms ms', ms = ms' -> implXM RNG c s Q ms' -> implXM RNG c s Q ms.
  Proof. intros X RNG c s Q ms ms' -> H. exact H. Qed.

  #[using="Type"] Lemma implXM_ret_l : forall {A B} RNG (v : A) (k : A -> M B) s Q ms,
    implXM RNG (k v) s Q ms -> implXM RNG (mbind (mret v) k) s Q ms.
  Proof. intros. exact H. Qed.
  #[using="Type"] Lemma implXM_unr_l : forall {A B} RNG (k : A -> M B) s Q ms, implXM RNG (mbind munr k) s Q ms.
  Proof. intros. apply implXM_unr. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma implXM_evt : forall {A} RNG (c : M A) s Q P ms,
    evtF asegs RNG P ms -> (forall ms', P ms' -> implXM RNG c s Q ms') -> implXM RNG c s Q ms.
  Proof. intros A RNG c s Q P ms H K. unfold implXM in *. eapply implF_evtF; eauto. Qed.
  #[using="Type"] Lemma implXM_from_evt : forall {A} RNG (c : M A) s Q ms,
    evtF asegs RNG (fun ms' => implXM RNG c s Q ms') ms -> implXM RNG c s Q ms.
  Proof. intros A RNG c s Q ms H. eapply implXM_evt; [exact H|]. intros ms' H'; exact H'. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma implXM_teq : forall {A} RNG (c c' : M A) s Q ms, mteq c c' -> implXM RNG c s Q ms -> implXM RNG c' s Q ms.
  Proof. intros A RNG c c' s Q ms H HI. unfold implXM in *. eapply (implF_teq asegs); [apply H| exact HI]. Qed.
End ImplXM.

(* [comment removed for export] *)
#[using="Type"] Lemma implXM_implAM : forall {St A} RNG (c : Monad.M St A) s Q ms,
  implXM (at_nodeA asegs) (silA ASHM) (npeekA asegs) fstepS RNG c s Q ms <-> implAM RNG c s Q ms.
Proof. intros. split; intros H; exact H. Qed.

(* [comment removed for export] *)
Definition px_atn : node -> footprint -> machine_state -> Prop := fun _ _ _ => False.
Definition px_sil : footprint -> machine_state -> machine_state -> Prop := fun _ _ _ => False.
Definition px_npk : node -> option (machine_state -> resp) := fun _ => None.
Definition px_fst : node -> resp -> footprint -> footprint -> Prop := fun _ _ _ _ => False.

#[using="Type"] Lemma px_evtS_evtF : forall RNG (Q : machine_state -> Prop) ms, @ITreeA.evtS asegs px_sil RNG Q ms -> evtF asegs RNG Q ms.
Proof.
  intros RNG Q ms (ms' & H & HQ). exists ms'. split; [| exact HQ].
  induction H as [ms0 | ms0 ms1 ms2 H1 _ IH | ms0 ms1 ms2 H1 _ _]; [constructor | econstructor; eauto | destruct H1].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implXM_pure_evtF : forall {St A} RNG (c : Monad.M St A) s (Q : A -> St -> machine_state -> Prop) ms a s',
  c s = Ret (Ok (a, s')) ->
  implXM px_atn px_sil px_npk px_fst RNG c s Q ms -> evtF asegs RNG (Q a s') ms.
Proof.
  intros St A RNG c s Q ms a s' E H. unfold implXM in H. rewrite E in H. cbn in H.
  apply px_evtS_evtF in H. eapply evtF_mono; [exact H|]. cbn. intros ms' [_ HQ]. exact HQ.
Qed.
End CANSEC1.
Arguments implXM atn sil_ npk_ fst_ {St A} RNG c s Q ms.

(* [comment removed for export] *)
Ltac ienterX := lazymatch goal with |- implXM _ _ _ _ _ _ _ _ _ => apply implXM_from_evt | _ => idtac end.
Ltac ileaveX := lazymatch goal with |- evtF _ _ _ _ => apply evtF_done | _ => idtac end;
                lazymatch goal with
                | |- @ITreeA.implF _ _ ?atn ?sil ?npk ?fst _ ?RNG (?c ?s) (epostF (postF ?RNG' ?Q)) ?ms => change (implXM atn sil npk fst RNG c s Q ms)
                | _ => idtac end.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_mlib.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_kit__A3W.MonadF2.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section ImplXM.
  Variable atn : node -> footprint -> machine_state -> Prop.
  Variable sil_ : footprint -> machine_state -> machine_state -> Prop.
  Variable npk_ : node -> option (machine_state -> resp).
  Variable fst_ : node -> resp -> footprint -> footprint -> Prop.
  Context {St : Type}.
  Local Notation M := (Monad.M St).
  Local Open Scope mspec_scope.
  Local Notation implF := (@ITreeA.implF node asegs atn sil_ npk_ fst_ _).

  Definition implXM {A} (RNG : footprint) (c : M A) (s : St) (Q : A -> St -> machine_state -> Prop) (ms : machine_state) : Prop :=
    implF RNG (c s) (epostF (postF RNG Q)) ms.

  #[using="Type"] Lemma implXM_ret : forall {A} RNG (a : A) s Q ms, evtF asegs RNG (Q a s) ms -> implXM RNG (mret a) s Q ms.
  Proof. intros A RNG a s Q ms H. unfold implXM, mret. apply implF_ret_ok. cbn. eapply evtF_mono; [exact H|]. intros; split; auto. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma implXM_retF : forall {A} RNG (Q : A -> St -> machine_state -> Prop) (p : A * St) ms,
    evtF asegs RNG (Q (fst p) (snd p)) ms -> implF RNG (Ret (Ok p)) (epostF (postF RNG Q)) ms.
  Proof. intros A RNG Q [a s] ms H. apply implF_ret_ok. cbn. eapply evtF_mono; [exact H|]. intros; split; auto. Qed.

  #[using="Type"] Lemma implXM_unr : forall {A} RNG s (Q : A -> St -> machine_state -> Prop) ms, implXM RNG munr s Q ms.
  Proof. intros. unfold implXM, munr. apply implF_ret_unr. Qed.

  #[using="Type"] Lemma implXM_bind : forall {A B} RNG (m : M A) (f : A -> M B) s Q1 Q ms,
    implXM RNG m s Q1 ms ->
    (forall a s' ms', Q1 a s' ms' -> implXM RNG (f a) s' Q ms') ->
    implXM RNG (mbind m f) s Q ms.
  Proof.
    intros A B RNG m f s Q1 Q ms Hm Hf. unfold implXM, mbind in *.
    eapply implF_ebind; [exact Hm|]. intros [a s'] RNG' ms' [-> H]. cbn in *. apply Hf. exact H.
  Qed.

  #[using="Type"] Lemma implXM_mono : forall {A} RNG (m : M A) s (Q Q' : A -> St -> machine_state -> Prop) ms,
    implXM RNG m s Q ms -> (forall a s' ms', Q a s' ms' -> Q' a s' ms') -> implXM RNG m s Q' ms.
  Proof.
    intros A RNG m s Q Q' ms H HQ. unfold implXM in *. eapply implF_epost_mono; [exact H|].
    intros [a s'] RNG' ms' [E H']; split; [exact E| apply HQ; exact H'].
  Qed.

  #[using="Type"] Lemma implXM_eq_ms : forall {X} RNG (c : M X) s Q ms ms', ms = ms' -> implXM RNG c s Q ms' -> implXM RNG c s Q ms.
  Proof. intros X RNG c s Q ms ms' -> H. exact H. Qed.

  #[using="Type"] Lemma implXM_ret_l : forall {A B} RNG (v : A) (k : A -> M B) s Q ms,
    implXM RNG (k v) s Q ms -> implXM RNG (mbind (mret v) k) s Q ms.
  Proof. intros. exact H. Qed.
  #[using="Type"] Lemma implXM_unr_l : forall {A B} RNG (k : A -> M B) s Q ms, implXM RNG (mbind munr k) s Q ms.
  Proof. intros. apply implXM_unr. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma implXM_evt : forall {A} RNG (c : M A) s Q P ms,
    evtF asegs RNG P ms -> (forall ms', P ms' -> implXM RNG c s Q ms') -> implXM RNG c s Q ms.
  Proof. intros A RNG c s Q P ms H K. unfold implXM in *. eapply implF_evtF; eauto. Qed.
  #[using="Type"] Lemma implXM_from_evt : forall {A} RNG (c : M A) s Q ms,
    evtF asegs RNG (fun ms' => implXM RNG c s Q ms') ms -> implXM RNG c s Q ms.
  Proof. intros A RNG c s Q ms H. eapply implXM_evt; [exact H|]. intros ms' H'; exact H'. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma implXM_teq : forall {A} RNG (c c' : M A) s Q ms, mteq c c' -> implXM RNG c s Q ms -> implXM RNG c' s Q ms.
  Proof. intros A RNG c c' s Q ms H HI. unfold implXM in *. eapply (implF_teq asegs); [apply H| exact HI]. Qed.
End ImplXM.

(* [comment removed for export] *)
#[using="Type"] Lemma implXM_implAM : forall {St A} RNG (c : Monad.M St A) s Q ms,
  implXM (at_nodeA asegs) (silA ASHM) (npeekA asegs) fstepS RNG c s Q ms <-> implAM RNG c s Q ms.
Proof. intros. split; intros H; exact H. Qed.

(* [comment removed for export] *)
Definition px_atn : node -> footprint -> machine_state -> Prop := fun _ _ _ => False.
Definition px_sil : footprint -> machine_state -> machine_state -> Prop := fun _ _ _ => False.
Definition px_npk : node -> option (machine_state -> resp) := fun _ => None.
Definition px_fst : node -> resp -> footprint -> footprint -> Prop := fun _ _ _ _ => False.

#[using="Type"] Lemma px_evtS_evtF : forall RNG (Q : machine_state -> Prop) ms, @ITreeA.evtS asegs px_sil RNG Q ms -> evtF asegs RNG Q ms.
Proof.
  intros RNG Q ms (ms' & H & HQ). exists ms'. split; [| exact HQ].
  induction H as [ms0 | ms0 ms1 ms2 H1 _ IH | ms0 ms1 ms2 H1 _ _]; [constructor | econstructor; eauto | destruct H1].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implXM_pure_evtF : forall {St A} RNG (c : Monad.M St A) s (Q : A -> St -> machine_state -> Prop) ms a s',
  c s = Ret (Ok (a, s')) ->
  implXM px_atn px_sil px_npk px_fst RNG c s Q ms -> evtF asegs RNG (Q a s') ms.
Proof.
  intros St A RNG c s Q ms a s' E H. unfold implXM in H. rewrite E in H. cbn in H.
  apply px_evtS_evtF in H. eapply evtF_mono; [exact H|]. cbn. intros ms' [_ HQ]. exact HQ.
Qed.
End CANSEC1.
Arguments implXM atn sil_ npk_ fst_ {St A} RNG c s Q ms.

(* [comment removed for export] *)
Ltac ienterX := lazymatch goal with |- implXM _ _ _ _ _ _ _ _ _ => apply implXM_from_evt | _ => idtac end.
Ltac ileaveX := lazymatch goal with |- evtF _ _ _ _ => apply evtF_done | _ => idtac end;
                lazymatch goal with
                | |- @ITreeA.implF _ _ ?atn ?sil ?npk ?fst _ ?RNG (?c ?s) (epostF (postF ?RNG' ?Q)) ?ms => change (implXM atn sil npk fst RNG c s Q ms)
                | _ => idtac end.
End TwB.
