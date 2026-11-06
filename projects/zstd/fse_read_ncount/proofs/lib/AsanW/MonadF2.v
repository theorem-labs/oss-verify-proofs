(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import Printf_mlib.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg AProto MonadF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

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
End Teq.
Section ImplFTeq.
Context {node : Type}.
Variable segs : list Segment.
Variable atn : node -> footprint -> machine_state -> Prop.
Variable fst_ : node -> resp -> footprint -> footprint -> Prop.
Local Notation implF := (@ITreeA.implF node segs atn fst_ _).
#[using="Type"] Lemma implF_teq : forall {A} RNG (t t' : itree node A) Q ms, teq t t' -> implF RNG t Q ms -> implF RNG t' Q ms.
Proof.
intros A RNG t t' Q ms H; revert RNG ms. induction H as [r|n k k' Hk IH]; intros RNG ms Hi; cbn in *.
- exact Hi.
- eapply evtF_mono; [exact Hi|]. intros ms1 [Hat HK]. split; [exact Hat|]. intros rsp RNG' HF. apply IH. apply HK. exact HF.
Qed.
End ImplFTeq.
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
End CANSEC1.
Ltac massocF :=
repeat lazymatch goal with
| |- implAM _ (mbind (mbind _ _) _) _ _ _ => apply implAM_assoc
| |- implAM _ (mbind (mret _) _) _ _ _ => apply implAM_ret_l
end.
