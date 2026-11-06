(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import ShapeAlg HaltsKit.
From OSSVerify.Proofs.openssl.pem.lib Require Import Spec.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.

(* [comment removed for export] *)

Lemma snoc_cases : forall {A} (l : list A), l = [] \/ exists l' a, l = l' ++ [a].
Proof.
  intros A l. induction l as [| x l IH] using rev_ind; [left; reflexivity |].
  right. exists l, x. reflexivity.
Qed.

Lemma t_emit_last : forall evs T tr e,
  t_emit evs T (tr ++ [e]) -> In e evs \/ exists tr', T (tr' ++ [e]).
Proof.
  intros evs T tr e [Hp | (tr' & Heq & HT)].
  - left. apply (in_is_prefix e (tr ++ [e]) evs Hp). apply in_app_iff. right. left. reflexivity.
  - destruct (snoc_cases tr') as [-> | (l' & a & ->)].
    + left. rewrite app_nil_r in Heq. rewrite <- Heq. apply in_app_iff. right. left. reflexivity.
    + right. exists l'. rewrite app_assoc in Heq.
      destruct (app_inj_tail tr (evs ++ l') e a Heq) as [_ ->]. exact HT.
Qed.

Lemma t_nil_last : forall tr (e : event), ~ t_nil (tr ++ [e]).
Proof. intros tr e H. unfold t_nil in H. destruct tr; discriminate H. Qed.

Lemma t_exit_last : forall code fs tr e,
  t_exit code fs (tr ++ [e]) -> e = ExitEv code fs.
Proof.
  intros code fs tr e H. unfold t_exit in H.
  apply t_emit_last in H as [Hin | (tr' & HT)].
  - destruct Hin as [<- | []]. reflexivity.
  - exfalso. exact (t_nil_last tr' e HT).
Qed.

Lemma t_alt2_last : forall A B tr (e : event),
  t_alt2 A B (tr ++ [e]) -> A (tr ++ [e]) \/ B (tr ++ [e]).
Proof. intros A B tr e H. exact H. Qed.

(* [comment removed for export] *)
Lemma W_exit_free : forall ch s code fs, ~ In (ExitEv code fs) (W ch s).
Proof.
  intros ch s code fs H. unfold W in H. apply in_map_iff in H as (b & Hb & _). discriminate Hb.
Qed.

Lemma W_kill_free : forall ch s sig fs, ~ In (KillEv sig fs) (W ch s).
Proof.
  intros ch s sig fs H. unfold W in H. apply in_map_iff in H as (b & Hb & _). discriminate Hb.
Qed.

(* [comment removed for export] *)
Lemma emit_W_exit_last : forall ch s code fs tr e,
  t_emit (W ch s) (t_exit code fs) (tr ++ [e]) -> In e (W ch s) \/ e = ExitEv code fs.
Proof.
  intros ch s code fs tr e H. apply t_emit_last in H as [Hin | (tr' & HT)].
  - left. exact Hin.
  - right. exact (t_exit_last code fs tr' e HT).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition last_ok (fs : Fs.Fs) (e : event) : Prop :=
  (exists ch s, In e (W ch s)) \/ e = ExitEv (exit_code 2) fs \/ e = ExitEv (exit_code 0) fs.

Lemma t_die_last : forall msg fs tr e, t_die msg fs (tr ++ [e]) -> last_ok fs e.
Proof.
  intros msg fs tr e H. unfold t_die in H.
  apply emit_W_exit_last in H as [Hin | ->].
  - left. exists 2%Z, msg. exact Hin.
  - right. left. reflexivity.
Qed.

Lemma t_target_last : forall data fs tr e, t_target data fs (tr ++ [e]) -> last_ok fs e.
Proof.
  intros data fs tr e H. unfold t_target in H.
  apply emit_W_exit_last in H as [Hin | ->].
  - left. exists 1%Z, (zero_lines (calls_of data)). exact Hin.
  - right. right. reflexivity.
Qed.

Lemma t_body_last : forall data fs tr e, t_body data fs (tr ++ [e]) -> last_ok fs e.
Proof.
  intros data fs tr e H. unfold t_body, t_body_cfg in H.
  destruct (MAX_INPUT <=? Z.of_nat (length data))%Z; [exact (t_die_last _ fs tr e H) |].
  destruct (length data <? HDR_MIN)%nat; [exact (t_die_last _ fs tr e H) |].
  destruct (length data <? HDR_MIN + config_len data)%nat; [exact (t_die_last _ fs tr e H) |].
  exact (t_target_last data fs tr e H).
Qed.

Lemma spec_last : forall argv fs tr e, Spec.spec argv fs (tr ++ [e]) -> last_ok fs e.
Proof.
  intros argv fs tr e H. unfold spec, spec_cfg in H.
  destruct (drv_classify argv fs) as [| path | path | path data].
  - exact (t_die_last _ fs tr e H).
  - exact (t_die_last _ fs tr e H).
  - destruct H as [H | H]; exact (t_die_last _ fs tr e H).
  - destruct H as [H | H]; [exact (t_die_last _ fs tr e H) |].
    change (t_body data fs (tr ++ [e])) in H. exact (t_body_last data fs tr e H).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition spec_codes : list word := [Z_to_bv 64 0; Z_to_bv 64 2].

Theorem spec_exits_in : forall argv fs, exits_in spec_codes (Spec.spec argv fs).
Proof.
  intros argv fs tr code fs' H.
  destruct (spec_last argv fs tr _ H) as [(ch & s & Hin) | [He | He]].
  - exfalso. exact (W_exit_free ch s code fs' Hin).
  - injection He as -> _. right. left. reflexivity.
  - injection He as -> _. left. reflexivity.
Qed.

Theorem spec_kill_free : forall argv fs, kill_free (Spec.spec argv fs).
Proof.
  intros argv fs tr sig fs' H.
  destruct (spec_last argv fs tr _ H) as [(ch & s & Hin) | [He | He]].
  - exact (W_kill_free ch s sig fs' Hin).
  - discriminate He.
  - discriminate He.
Qed.
