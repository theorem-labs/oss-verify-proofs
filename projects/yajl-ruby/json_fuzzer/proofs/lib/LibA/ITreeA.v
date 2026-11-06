(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Exec.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Export ITree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import ExecA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.

Section ITreeA.
Variable node : Type.
Variable segs : list Segment.
(* [comment removed for export] *)
Variable at_nodeP : (acc -> Prop) -> node -> machine_state -> Prop.

Local Notation itreeN := (itree node).

Section WithPolicy.
Variable P : acc -> Prop.

Fixpoint implA {R} (t : itreeN R) (Q : R -> machine_state -> Prop) (ms : machine_state) : Prop :=
  match t with
  | Ret r => evtA segs P (Q r) ms
  | Vis n k => evtA segs P (fun ms1 => at_nodeP P n ms1 /\ forall rsp, implA (k rsp) Q (nret ms1 rsp)) ms
  end.

Lemma implA_ret_intro : forall {R} (r : R) Q ms, evtA segs P (Q r) ms -> implA (Ret r) Q ms.
Proof. intros. exact H. Qed.

Lemma implA_mono : forall {R} (t : itreeN R) (Q Q' : R -> machine_state -> Prop) ms,
  implA t Q ms -> (forall r ms', Q r ms' -> Q' r ms') -> implA t Q' ms.
Proof.
  induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
  - eapply evtA_mono; eauto.
  - eapply evtA_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp. eapply IH; eauto.
Qed.

(* [comment removed for export] *)
Lemma implA_evtA : forall {R} (t : itreeN R) Q P0 ms,
  evtA segs P P0 ms -> (forall ms', P0 ms' -> implA t Q ms') -> implA t Q ms.
Proof.
  intros R t Q P0 ms H K. destruct t; cbn in *; eapply evtA_cut; eauto; intros ms' HP; apply (K _ HP).
Qed.

(* [comment removed for export] *)
Lemma implA_bind : forall {A B} (t : itreeN A) (f : A -> itreeN B) Q1 Q ms,
  implA t Q1 ms -> (forall r ms', Q1 r ms' -> implA (f r) Q ms') -> implA (bind node t f) Q ms.
Proof.
  induction t as [r|n k IH]; intros f Q1 Q ms H Hf; cbn [bind].
  - cbn in H. eapply implA_evtA; [exact H|]. intros ms' HQ. exact (Hf _ _ HQ).
  - cbn in H |- *. eapply evtA_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.

(* [comment removed for export] *)
Lemma implA_ret_unr : forall {A} (Q : A -> machine_state -> Prop) ms, implA (Ret Unr) (epost Q) ms.
Proof. intros A Q ms. cbn. apply evtA_done. exact I. Qed.

Lemma implA_ret_ok : forall {A} (Q : A -> machine_state -> Prop) a ms,
  evtA segs P (Q a) ms -> implA (Ret (Ok a)) (epost Q) ms.
Proof. intros A Q a ms H. exact H. Qed.

Lemma implA_ebind : forall {A B} (t : itreeN (exc A)) (f : A -> itreeN (exc B)) Q1 Q ms,
  implA t (epost Q1) ms -> (forall a ms', Q1 a ms' -> implA (f a) (epost Q) ms') ->
  implA (ebind t f) (epost Q) ms.
Proof.
  intros A B t f Q1 Q ms Ht Hf. unfold ebind. eapply implA_bind; [exact Ht|].
  intros [|a] ms' H'; cbn in H'.
  - apply implA_ret_unr.
  - apply Hf. exact H'.
Qed.

Lemma implA_epost_mono : forall {A} (t : itreeN (exc A)) (Q Q' : A -> machine_state -> Prop) ms,
  implA t (epost Q) ms -> (forall a ms', Q a ms' -> Q' a ms') -> implA t (epost Q') ms.
Proof.
  intros A t Q Q' ms H HQ. eapply implA_mono; [exact H|]. intros [|a] ms'; cbn; auto.
Qed.

Lemma implA_enode : forall {A} n (pl : resp -> option A) (Q : A -> machine_state -> Prop) ms,
  evtA segs P (fun ms1 => at_nodeP P n ms1 /\ forall rsp a, pl rsp = Some a -> evtA segs P (Q a) (nret ms1 rsp)) ms ->
  implA (enode n pl) (epost Q) ms.
Proof.
  intros A n pl Q ms H. cbn. eapply evtA_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp. specialize (Hk rsp). destruct (pl rsp) as [a|]; cbn.
  - apply Hk. reflexivity.
  - apply evtA_done. exact I.
Qed.

(* [comment removed for export] *)
Lemma implA_impl : forall {R} (t : itreeN R) Q ms,
  implA t Q ms -> impl segs (fun n ms => at_nodeP P n ms) t Q ms.
Proof.
  induction t as [r|n k IH]; intros Q ms H; cbn in *.
  - eapply evtA_evt; exact H.
  - apply evtA_evt in H. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp; apply IH, Hk.
Qed.

End WithPolicy.

Lemma implA_weaken : forall (P P' : acc -> Prop) {R} (t : itreeN R) Q ms,
  (forall x, P x -> P' x) ->
  (forall n ms, at_nodeP P n ms -> at_nodeP P' n ms) ->
  implA P t Q ms -> implA P' t Q ms.
Proof.
  intros P P' R t; induction t as [r|n k IH]; intros Q ms HPP Hat H; cbn in *.
  - eapply evtA_weaken; eauto.
  - eapply evtA_weaken in H; [|exact HPP]. eapply evtA_mono; [exact H|].
    intros ms1 [H1 H2]. split; [apply Hat; exact H1|]. intros rsp. apply IH; auto.
Qed.

End ITreeA.

Arguments implA {node} segs at_nodeP P {R} t Q ms.
