(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import ShapeAlg Spec BigintSpec HaltsBridge.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require PropExec.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable S : list word.
Hypothesis S0 : In (exit_code 0) S.
Hypothesis S2 : In (exit_code 2) S.

Lemma In_W_not_exit : forall ch s code fs, ~ In (ExitEv code fs) (W ch s).
Proof. intros ch s code fs H. unfold W in H. apply in_map_iff in H as (b & Hb & _). discriminate Hb. Qed.
Lemma In_W_not_kill : forall ch s sig fs, ~ In (KillEv sig fs) (W ch s).
Proof. intros ch s sig fs H. unfold W in H. apply in_map_iff in H as (b & Hb & _). discriminate Hb. Qed.

Lemma In_prefix : forall (A : Type) (x : A) tr evs, is_prefix tr evs -> In x tr -> In x evs.
Proof.
  intros A x tr; induction tr as [|y tr IH]; intros evs Hpre Hin; [destruct Hin |].
  destruct evs as [|z evs]; [destruct Hpre |]. destruct Hpre as [<- Hpre].
  destruct Hin as [<- | Hin]; [left; reflexivity | right; exact (IH _ Hpre Hin)].
Qed.

Lemma codes_ok_nil : codes_ok S t_nil.
Proof. intros tr code fs Htr Hin. unfold t_nil in Htr. subst tr. destruct Hin. Qed.
Lemma nokill_nil : nokill t_nil.
Proof. intros tr sig fs Htr Hin. unfold t_nil in Htr. subst tr. destruct Hin. Qed.

Lemma codes_ok_emit : forall evs T,
  (forall code fs, In (ExitEv code fs) evs -> In code S) -> codes_ok S T -> codes_ok S (t_emit evs T).
Proof.
  intros evs T Hevs HT tr code fs [Hpre | (tr' & -> & Htr')] Hin.
  - apply (Hevs code fs). exact (In_prefix _ _ _ _ Hpre Hin).
  - apply in_app_iff in Hin as [Hin | Hin]; [exact (Hevs _ _ Hin) | exact (HT _ _ _ Htr' Hin)].
Qed.
Lemma nokill_emit : forall evs T,
  (forall sig fs, ~ In (KillEv sig fs) evs) -> nokill T -> nokill (t_emit evs T).
Proof.
  intros evs T Hevs HT tr sig fs [Hpre | (tr' & -> & Htr')] Hin.
  - apply (Hevs sig fs). exact (In_prefix _ _ _ _ Hpre Hin).
  - apply in_app_iff in Hin as [Hin | Hin]; [exact (Hevs _ _ Hin) | exact (HT _ _ _ Htr' Hin)].
Qed.

Lemma codes_ok_exit : forall z fs, In (exit_code z) S -> codes_ok S (t_exit (exit_code z) fs).
Proof.
  intros z fs Hz. unfold t_exit. apply codes_ok_emit; [| apply codes_ok_nil].
  intros code fs' [H | []]. injection H as <- _. exact Hz.
Qed.
Lemma nokill_exit : forall c fs, nokill (t_exit c fs).
Proof.
  intros c fs. unfold t_exit. apply nokill_emit; [| apply nokill_nil].
  intros sig fs' [H | []]. discriminate H.
Qed.

Lemma codes_ok_die : forall msg fs, codes_ok S (t_die msg fs).
Proof.
  intros msg fs. unfold t_die. apply codes_ok_emit; [| apply codes_ok_exit; exact S2].
  intros code fs' H. exfalso. exact (In_W_not_exit _ _ _ _ H).
Qed.
Lemma nokill_die : forall msg fs, nokill (t_die msg fs).
Proof.
  intros msg fs. unfold t_die. apply nokill_emit; [| apply nokill_exit].
  intros sig fs' H. exact (In_W_not_kill _ _ _ _ H).
Qed.

Lemma codes_ok_alt2 : forall A B, codes_ok S A -> codes_ok S B -> codes_ok S (t_alt2 A B).
Proof. intros A B HA HB tr code fs [H | H] Hin; [exact (HA _ _ _ H Hin) | exact (HB _ _ _ H Hin)]. Qed.
Lemma nokill_alt2 : forall A B, nokill A -> nokill B -> nokill (t_alt2 A B).
Proof. intros A B HA HB tr sig fs [H | H] Hin; [exact (HA _ _ _ H Hin) | exact (HB _ _ _ H Hin)]. Qed.

Lemma codes_ok_body : forall data fs, codes_ok S (t_body data fs).
Proof.
  intros data fs. unfold t_body.
  destruct (MAX_INPUT <=? Z.of_nat (length data))%Z; [apply codes_ok_die |].
  destruct (length data <? 6)%nat; [apply codes_ok_die |].
  destruct (length data <? _)%nat; [apply codes_ok_die |].
  apply codes_ok_emit; [| apply codes_ok_exit; exact S0].
  intros code fs' H. exfalso. exact (In_W_not_exit _ _ _ _ H).
Qed.
Lemma nokill_body : forall data fs, nokill (t_body data fs).
Proof.
  intros data fs. unfold t_body.
  destruct (MAX_INPUT <=? Z.of_nat (length data))%Z; [apply nokill_die |].
  destruct (length data <? 6)%nat; [apply nokill_die |].
  destruct (length data <? _)%nat; [apply nokill_die |].
  apply nokill_emit; [| apply nokill_exit].
  intros sig fs' H. exact (In_W_not_kill _ _ _ _ H).
Qed.

Theorem codes_ok_spec : forall argv fs, codes_ok S (spec argv fs).
Proof.
  intros argv fs. unfold spec.
  destruct argv as [| a0 [| path [| x rest]]]; try apply codes_ok_die.
  destruct (4096 <=? length path)%nat; [apply codes_ok_die |].
  destruct (list_byte_eqb path []); [apply codes_ok_die |].
  destruct (list_byte_eqb path dot_path); [apply codes_ok_alt2; apply codes_ok_die |].
  destruct (fs_lookup fs path); [| apply codes_ok_die].
  apply codes_ok_alt2; [apply codes_ok_die | apply codes_ok_body].
Qed.

Theorem nokill_spec : forall argv fs, nokill (spec argv fs).
Proof.
  intros argv fs. unfold spec.
  destruct argv as [| a0 [| path [| x rest]]]; try apply nokill_die.
  destruct (4096 <=? length path)%nat; [apply nokill_die |].
  destruct (list_byte_eqb path []); [apply nokill_die |].
  destruct (list_byte_eqb path dot_path); [apply nokill_alt2; apply nokill_die |].
  destruct (fs_lookup fs path); [| apply nokill_die].
  apply nokill_alt2; [apply nokill_die | apply nokill_body].
Qed.

End FPX_1.
