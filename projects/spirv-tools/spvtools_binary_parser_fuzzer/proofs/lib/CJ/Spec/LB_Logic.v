(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import Monad MSafe.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Definition live (mo : Model) : Z := vm_live_bytes (m_vmmaps mo).

Fixpoint twl {R} (B : Z) (t : itree node R) (mo : Model) (P : R -> Model -> Prop) : Prop :=
  match t with
  | Ret r => P r mo
  | Vis n k => forall rsp mo' evs, nstep n mo rsp mo' evs -> live mo' <= B /\ twl B (k rsp) mo' P
  end.

Lemma twl_mono : forall {R} B (t : itree node R) mo (P P' : R -> Model -> Prop),
  twl B t mo P -> (forall r mo1, P r mo1 -> P' r mo1) -> twl B t mo P'.
Proof.
  intros R B t. induction t as [r|n k IH]; intros mo P P' H HP; cbn in *.
  - apply HP. exact H.
  - intros rsp mo' evs Hst. destruct (H rsp mo' evs Hst) as [HB Hk]. split; [exact HB|]. eapply IH; eauto.
Qed.

Lemma twl_bind : forall {A R} B (t : itree node A) (f : A -> itree node R) mo (P : R -> Model -> Prop),
  twl B t mo (fun a mo1 => twl B (f a) mo1 P) -> twl B (ITree.bind node t f) mo P.
Proof.
  intros A R B t. induction t as [r|n k IH]; intros f mo P H; cbn in *.
  - exact H.
  - intros rsp mo' evs Hst. destruct (H rsp mo' evs Hst) as [HB Hk]. split; [exact HB|]. apply IH. exact Hk.
Qed.

Definition etwl {A} (B : Z) (t : itree node (exc A)) (mo : Model) (Q : A -> Model -> Prop) : Prop :=
  twl B t mo (fun r mo1 => match r with Unr => True | Ok a => Q a mo1 end).

Lemma etwl_mono : forall {A} B (t : itree node (exc A)) mo (Q Q' : A -> Model -> Prop),
  etwl B t mo Q -> (forall a mo1, Q a mo1 -> Q' a mo1) -> etwl B t mo Q'.
Proof.
  intros A B t mo Q Q' H HQ. unfold etwl in *. eapply twl_mono; [exact H|]. intros [|a] mo1; cbn; auto.
Qed.

Lemma etwl_ebind : forall {A C} B (t : itree node (exc A)) (f : A -> itree node (exc C)) mo Q,
  etwl B t mo (fun a mo1 => etwl B (f a) mo1 Q) -> etwl B (ebind t f) mo Q.
Proof.
  intros A C B t f mo Q H. unfold etwl, ebind in *. apply twl_bind.
  eapply twl_mono; [exact H|]. intros [|a] mo1 Ha; cbn; [exact I| exact Ha].
Qed.

Fixpoint flat {R} (t : itree node R) : Prop :=
  match t with
  | Ret _ => True
  | Vis n k => forall rsp, match k rsp with Ret _ => True | Vis _ _ => False end
  end.

Section MSpecL.
Context {St : Type}.
Variable B : Z.

Definition mspecL {A} (P : assn St) (m : M St A) (Q : A -> assn St) : Prop :=
  forall s mo, P s mo -> etwl B (m s) mo (fun p mo' => Q (fst p) (snd p) mo').

Lemma mspecL_ret {A} (a : A) (P : assn St) (Q : A -> assn St) :
  (forall s mo, P s mo -> Q a s mo) -> mspecL P (mret a) Q.
Proof. intros H s mo HP. cbn. apply H. exact HP. Qed.

Lemma mspecL_bind {A C} (m : M St A) (f : A -> M St C) (P : assn St) (Q1 : A -> assn St) (Q : C -> assn St) :
  mspecL P m Q1 -> (forall a, mspecL (Q1 a) (f a) Q) -> mspecL P (mbind m f) Q.
Proof.
  intros Hm Hf s mo HP. unfold mbind. apply etwl_ebind.
  eapply etwl_mono; [exact (Hm s mo HP)|]. intros [a s1] mo1 H1. cbn in *. exact (Hf a s1 mo1 H1).
Qed.

Lemma mspecL_conseq {A} (m : M St A) (P P' : assn St) (Q Q' : A -> assn St) :
  mspecL P m Q -> (forall s mo, P' s mo -> P s mo) -> (forall a s mo, Q a s mo -> Q' a s mo) -> mspecL P' m Q'.
Proof.
  intros Hm HP HQ s mo HP'. eapply etwl_mono; [exact (Hm s mo (HP _ _ HP'))|]. intros [a s1] mo1; cbn; auto.
Qed.

Lemma mspecL_pre {A} (m : M St A) (P P' : assn St) (Q : A -> assn St) :
  mspecL P m Q -> (forall s mo, P' s mo -> P s mo) -> mspecL P' m Q.
Proof. intros Hm HP. eapply mspecL_conseq; eauto. Qed.

Lemma mspecL_get (P : assn St) : mspecL P mget (fun s' s mo => s' = s /\ P s mo).
Proof. intros s mo HP. cbn. auto. Qed.

Lemma mspecL_upd' (P : assn St) (Q : unit -> assn St) (f : St -> St) :
  (forall s mo, P s mo -> Q tt (f s) mo) -> mspecL P (mupd f) Q.
Proof. intros H s mo HP. cbn. apply H. exact HP. Qed.

Lemma mspecL_pointwise {A} (P : assn St) (m : M St A) (Q : A -> assn St) :
  (forall s mo, P s mo -> mspecL (fun s' mo' => s' = s /\ mo' = mo) m Q) -> mspecL P m Q.
Proof. intros H s mo HP. apply (H s mo HP). auto. Qed.

Lemma mspecL_seq {A C} (m : M St A) (f : A -> M St C) (P R : assn St) (Q : C -> assn St) :
  mspecL P m (fun _ => R) -> (forall a, mspecL R (f a) Q) -> mspecL P (mbind m f) Q.
Proof. intros Hm Hf. eapply mspecL_bind; [exact Hm|]. intros a. apply Hf. Qed.

Fixpoint pure_tree {R} (t : itree node R) : Prop := match t with Ret _ => True | Vis _ _ => False end.

End MSpecL.
End AC_1.

Arguments mspecL {ACEIL St} B {A} P m Q.
