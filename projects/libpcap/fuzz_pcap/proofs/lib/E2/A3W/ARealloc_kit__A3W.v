(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Exec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_mlib__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MonadF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module ARealloc_kit.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg AProto.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma implS_sbind : forall {A B} (t : AM A) (f : A -> AM B) RNG
    (Q1 : A -> footprint -> machine_state -> Prop) (Q : B -> footprint -> machine_state -> Prop) ms,
  implS asegs RNG (aembed ATOP t) (epostF Q1) ms ->
  (forall a RNG' ms', Q1 a RNG' ms' -> implS asegs RNG' (aembed ATOP (f a)) (epostF Q) ms') ->
  implS asegs RNG (aembed ATOP (sbind t f)) (epostF Q) ms.
Proof.
  intros A B t f. induction t as [a|e k IH]; intros RNG Q1 Q ms H Hf.
  - rewrite aembed_sbind_ret. rewrite aembed_ret in H.
    eapply implF_evtS; [exact H|]. cbn. intros ms' HQ. exact (Hf _ _ _ HQ).
  - rewrite aembed_sbind_vis. rewrite aembed_vis in H.
    destruct e; cbn [aev_tree] in H |- *; try (apply implF_ret_unr).
    all: unfold enode in H |- *; rewrite ebind_vis in H |- *; cbn [implF] in H |- *.
    all: eapply evtS_mono; [exact H|]; intros ms1 [[Hat Hk]|(g & Hg & Hk)];
      [ left; split; [exact Hat|]; intros rsp RNG' HF; specialize (Hk rsp RNG' HF)
      | right; exists g; split; [exact Hg|]; intros RNG' HF; specialize (Hk RNG' HF) ].
    all: lazymatch goal with |- context [ebind (match ?pl with Some _ => _ | None => _ end) _] => destruct pl as [z|] end.
    all: first [ rewrite ebind_ret_ok in Hk |- *; eapply IH; [exact Hk| exact Hf] | rewrite ebind_ret_unr; apply implF_ret_unr ].
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma implS_sbind : forall {A B} (t : AM A) (f : A -> AM B) RNG
    (Q1 : A -> footprint -> machine_state -> Prop) (Q : B -> footprint -> machine_state -> Prop) ms,
  implS asegs RNG (aembed ATOP t) (epostF Q1) ms ->
  (forall a RNG' ms', Q1 a RNG' ms' -> implS asegs RNG' (aembed ATOP (f a)) (epostF Q) ms') ->
  implS asegs RNG (aembed ATOP (sbind t f)) (epostF Q) ms.
Proof.
  intros A B t f. induction t as [a|e k IH]; intros RNG Q1 Q ms H Hf.
  - rewrite aembed_sbind_ret. rewrite aembed_ret in H.
    eapply implF_evtS; [exact H|]. cbn. intros ms' HQ. exact (Hf _ _ _ HQ).
  - rewrite aembed_sbind_vis. rewrite aembed_vis in H.
    destruct e; cbn [aev_tree] in H |- *; try (apply implF_ret_unr).
    all: unfold enode in H |- *; rewrite ebind_vis in H |- *; cbn [implF] in H |- *.
    all: eapply evtS_mono; [exact H|]; intros ms1 [[Hat Hk]|(g & Hg & Hk)];
      [ left; split; [exact Hat|]; intros rsp RNG' HF; specialize (Hk rsp RNG' HF)
      | right; exists g; split; [exact Hg|]; intros RNG' HF; specialize (Hk RNG' HF) ].
    all: lazymatch goal with |- context [ebind (match ?pl with Some _ => _ | None => _ end) _] => destruct pl as [z|] end.
    all: first [ rewrite ebind_ret_ok in Hk |- *; eapply IH; [exact Hk| exact Hf] | rewrite ebind_ret_unr; apply implF_ret_unr ].
Qed.
End CANSEC1.
End TwB.
End ARealloc_kit.

(* [comment removed for export] *)
Module MonadF2.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_mlib__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_mlib.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg AProto MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Section CANSEC1. Context {rc : runConstT}.
Section Teq.
  Context {node : Type}.

  #[using="Type"] Lemma teq_refl : forall {A} (t : itree node A), teq t t.
  Proof. induction t; constructor; auto. Qed.

  #[using="Type"] Lemma teq_sym : forall {A} (t t' : itree node A), teq t t' -> teq t' t.
  Proof. intros A t t' H; induction H; constructor; auto. Qed.

  #[using="Type"] Lemma teq_trans : forall {A} (t1 t2 t3 : itree node A), teq t1 t2 -> teq t2 t3 -> teq t1 t3.
  Proof.
    intros A t1 t2 t3 H12; revert t3. induction H12 as [r|n k k' Hk IH]; intros t3 H23.
    - exact H23.
    - inversion H23; subst. constructor. intros x. apply IH. auto.
  Qed.

  #[using="Type"] Lemma teq_bind_cong : forall {A B} (t : itree node A) (f g : A -> itree node B),
    (forall x, teq (f x) (g x)) -> teq (ITree.bind node t f) (ITree.bind node t g).
  Proof. induction t as [r|n k IH]; intros f g H; cbn; [apply H| constructor; intros x; apply IH; exact H]. Qed.

  #[using="Type"] Lemma teq_bind_assoc : forall {A B C} (t : itree node A) (f : A -> itree node B) (g : B -> itree node C),
    teq (ITree.bind node (ITree.bind node t f) g) (ITree.bind node t (fun x => ITree.bind node (f x) g)).
  Proof. induction t as [r|n k IH]; intros f g; cbn; [apply teq_refl| constructor; intros x; apply IH]. Qed.

  #[using="Type"] Lemma teq_bind_l : forall {A B} (t t' : itree node A) (f : A -> itree node B),
    teq t t' -> teq (ITree.bind node t f) (ITree.bind node t' f).
  Proof. intros A B t t' f H; induction H; cbn; [apply teq_refl| constructor; auto]. Qed.
End Teq.

Section ImplFTeq.
  Context {node : Type}.
  Variable segs : list Segment.
  Variable atn : node -> footprint -> machine_state -> Prop.
  Variable sil_ : footprint -> machine_state -> machine_state -> Prop.   (* [comment removed for export] *)
  Variable npk_ : node -> option (machine_state -> resp).                 (* [comment removed for export] *)
  Variable fst_ : node -> resp -> footprint -> footprint -> Prop.
  Local Notation implF := (@ITreeA.implF node segs atn sil_ npk_ fst_ _).

  #[using="Type"] Lemma implF_teq : forall {A} RNG (t t' : itree node A) Q ms, teq t t' -> implF RNG t Q ms -> implF RNG t' Q ms.
  Proof.
    intros A RNG t t' Q ms H; revert RNG ms. induction H as [r|n k k' Hk IH]; intros RNG ms Hi; cbn in *.
    - exact Hi.
    - eapply evtS_mono; [exact Hi|]. intros ms1 [[Hat HK]|(fpk & Hfpk & HK)].      (* [comment removed for export] *)
      + left. split; [exact Hat|]. intros rsp RNG' HF. apply IH. apply HK. exact HF.
      + right. exists fpk. split; [exact Hfpk|]. intros RNG' HF. apply IH. apply HK. exact HF.
  Qed.
End ImplFTeq.

(* [comment removed for export] *)
Section MTeq.
  Context {St : Type}.
  Local Notation M := (Monad.M St).
  Local Open Scope mspec_scope.

  Definition mteq {A} (c c' : M A) : Prop := forall s, teq (c s) (c' s).

  #[using="Type"] Lemma mteq_refl : forall {A} (c : M A), mteq c c.
  Proof. intros A c s. apply teq_refl. Qed.
  #[using="Type"] Lemma mteq_sym : forall {A} (c c' : M A), mteq c c' -> mteq c' c.
  Proof. intros A c c' H s. apply teq_sym. apply H. Qed.
  #[using="Type"] Lemma mteq_trans : forall {A} (c1 c2 c3 : M A), mteq c1 c2 -> mteq c2 c3 -> mteq c1 c3.
  Proof. intros A c1 c2 c3 H1 H2 s. eapply teq_trans; [apply H1 | apply H2]. Qed.

  #[using="Type"] Lemma mteq_assoc : forall {A B C} (a : M A) (b : A -> M B) (k : B -> M C),
    mteq (mbind (mbind a b) k) (mbind a (fun x => mbind (b x) k)).
  Proof.
    intros A B C a b k s. unfold mbind, ebind.
    eapply teq_trans; [apply teq_bind_assoc|]. apply teq_bind_cong. intros r; destruct r; cbn; apply teq_refl.
  Qed.

  #[using="Type"] Lemma mteq_cong : forall {A B} (a : M A) (f g : A -> M B),
    (forall x, mteq (f x) (g x)) -> mteq (mbind a f) (mbind a g).
  Proof.
    intros A B a f g H s. unfold mbind, ebind. apply teq_bind_cong. intros r; destruct r; cbn; first [apply H | apply teq_refl].
  Qed.

  #[using="Type"] Lemma mteq_ret_l : forall {A B} (v : A) (k : A -> M B), mteq (mbind (mret v) k) (k v).
  Proof. intros A B v k s. apply teq_refl. Qed.

  #[using="Type"] Lemma implAM_teq : forall {A} RNG (c c' : M A) s Q ms, mteq c c' -> implAM RNG c s Q ms -> implAM RNG c' s Q ms.
  Proof. intros A RNG c c' s Q ms H Hi. unfold implAM in *. eapply implF_teq; [apply H | exact Hi]. Qed.
End MTeq.

(* [comment removed for export] *)
End CANSEC1.
Ltac massocF :=
  repeat lazymatch goal with
  | |- implAM _ (mbind (mbind _ _) _) _ _ _ => apply implAM_assoc
  | |- implAM _ (mbind (mret _) _) _ _ _ => apply implAM_ret_l
  end.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_mlib.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Section CANSEC1. Context {rc : runConstT}.
Section Teq.
  Context {node : Type}.

  #[using="Type"] Lemma teq_refl : forall {A} (t : itree node A), teq t t.
  Proof. induction t; constructor; auto. Qed.

  #[using="Type"] Lemma teq_sym : forall {A} (t t' : itree node A), teq t t' -> teq t' t.
  Proof. intros A t t' H; induction H; constructor; auto. Qed.

  #[using="Type"] Lemma teq_trans : forall {A} (t1 t2 t3 : itree node A), teq t1 t2 -> teq t2 t3 -> teq t1 t3.
  Proof.
    intros A t1 t2 t3 H12; revert t3. induction H12 as [r|n k k' Hk IH]; intros t3 H23.
    - exact H23.
    - inversion H23; subst. constructor. intros x. apply IH. auto.
  Qed.

  #[using="Type"] Lemma teq_bind_cong : forall {A B} (t : itree node A) (f g : A -> itree node B),
    (forall x, teq (f x) (g x)) -> teq (ITree.bind node t f) (ITree.bind node t g).
  Proof. induction t as [r|n k IH]; intros f g H; cbn; [apply H| constructor; intros x; apply IH; exact H]. Qed.

  #[using="Type"] Lemma teq_bind_assoc : forall {A B C} (t : itree node A) (f : A -> itree node B) (g : B -> itree node C),
    teq (ITree.bind node (ITree.bind node t f) g) (ITree.bind node t (fun x => ITree.bind node (f x) g)).
  Proof. induction t as [r|n k IH]; intros f g; cbn; [apply teq_refl| constructor; intros x; apply IH]. Qed.

  #[using="Type"] Lemma teq_bind_l : forall {A B} (t t' : itree node A) (f : A -> itree node B),
    teq t t' -> teq (ITree.bind node t f) (ITree.bind node t' f).
  Proof. intros A B t t' f H; induction H; cbn; [apply teq_refl| constructor; auto]. Qed.
End Teq.

Section ImplFTeq.
  Context {node : Type}.
  Variable segs : list Segment.
  Variable atn : node -> footprint -> machine_state -> Prop.
  Variable sil_ : footprint -> machine_state -> machine_state -> Prop.   (* [comment removed for export] *)
  Variable npk_ : node -> option (machine_state -> resp).                 (* [comment removed for export] *)
  Variable fst_ : node -> resp -> footprint -> footprint -> Prop.
  Local Notation implF := (@ITreeA.implF node segs atn sil_ npk_ fst_ _).

  #[using="Type"] Lemma implF_teq : forall {A} RNG (t t' : itree node A) Q ms, teq t t' -> implF RNG t Q ms -> implF RNG t' Q ms.
  Proof.
    intros A RNG t t' Q ms H; revert RNG ms. induction H as [r|n k k' Hk IH]; intros RNG ms Hi; cbn in *.
    - exact Hi.
    - eapply evtS_mono; [exact Hi|]. intros ms1 [[Hat HK]|(fpk & Hfpk & HK)].      (* [comment removed for export] *)
      + left. split; [exact Hat|]. intros rsp RNG' HF. apply IH. apply HK. exact HF.
      + right. exists fpk. split; [exact Hfpk|]. intros RNG' HF. apply IH. apply HK. exact HF.
  Qed.
End ImplFTeq.

(* [comment removed for export] *)
Section MTeq.
  Context {St : Type}.
  Local Notation M := (Monad.M St).
  Local Open Scope mspec_scope.

  Definition mteq {A} (c c' : M A) : Prop := forall s, teq (c s) (c' s).

  #[using="Type"] Lemma mteq_refl : forall {A} (c : M A), mteq c c.
  Proof. intros A c s. apply teq_refl. Qed.
  #[using="Type"] Lemma mteq_sym : forall {A} (c c' : M A), mteq c c' -> mteq c' c.
  Proof. intros A c c' H s. apply teq_sym. apply H. Qed.
  #[using="Type"] Lemma mteq_trans : forall {A} (c1 c2 c3 : M A), mteq c1 c2 -> mteq c2 c3 -> mteq c1 c3.
  Proof. intros A c1 c2 c3 H1 H2 s. eapply teq_trans; [apply H1 | apply H2]. Qed.

  #[using="Type"] Lemma mteq_assoc : forall {A B C} (a : M A) (b : A -> M B) (k : B -> M C),
    mteq (mbind (mbind a b) k) (mbind a (fun x => mbind (b x) k)).
  Proof.
    intros A B C a b k s. unfold mbind, ebind.
    eapply teq_trans; [apply teq_bind_assoc|]. apply teq_bind_cong. intros r; destruct r; cbn; apply teq_refl.
  Qed.

  #[using="Type"] Lemma mteq_cong : forall {A B} (a : M A) (f g : A -> M B),
    (forall x, mteq (f x) (g x)) -> mteq (mbind a f) (mbind a g).
  Proof.
    intros A B a f g H s. unfold mbind, ebind. apply teq_bind_cong. intros r; destruct r; cbn; first [apply H | apply teq_refl].
  Qed.

  #[using="Type"] Lemma mteq_ret_l : forall {A B} (v : A) (k : A -> M B), mteq (mbind (mret v) k) (k v).
  Proof. intros A B v k s. apply teq_refl. Qed.

  #[using="Type"] Lemma implAM_teq : forall {A} RNG (c c' : M A) s Q ms, mteq c c' -> implAM RNG c s Q ms -> implAM RNG c' s Q ms.
  Proof. intros A RNG c c' s Q ms H Hi. unfold implAM in *. eapply implF_teq; [apply H | exact Hi]. Qed.
End MTeq.

(* [comment removed for export] *)
End CANSEC1.
Ltac massocF :=
  repeat lazymatch goal with
  | |- implAM _ (mbind (mbind _ _) _) _ _ _ => apply implAM_assoc
  | |- implAM _ (mbind (mret _) _) _ _ _ => apply implAM_ret_l
  end.
End TwB.
End MonadF2.
