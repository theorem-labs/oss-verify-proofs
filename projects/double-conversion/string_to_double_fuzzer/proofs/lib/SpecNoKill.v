(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ShapeAlg ShapeEF Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Lemma is_prefix_In {A} : forall (a l : list A) x, is_prefix a l -> In x a -> In x l.
Proof.
  induction a as [|y a IH]; intros l x Hp Hin; [destruct Hin|].
  destruct l as [|z l]; [cbn in Hp; contradiction|]. cbn in Hp. destruct Hp as [-> Hp].
  destruct Hin as [-> | Hin]; [left; reflexivity | right; exact (IH l x Hp Hin)].
Qed.

Lemma tset_no_kill_nil : tset_no_kill t_nil.
Proof. intros tr sig fs H Hin. unfold t_nil in H. subst tr. exact Hin. Qed.

Lemma tset_no_kill_emit : forall evs T,
  (forall sig fs, ~ In (KillEv sig fs) evs) -> tset_no_kill T -> tset_no_kill (t_emit evs T).
Proof.
  intros evs T He HT tr sig fs [Hp | (tr' & -> & Htr')] Hin.
  - exact (He sig fs (is_prefix_In _ _ _ Hp Hin)).
  - apply in_app_or in Hin. destruct Hin as [Hin | Hin]; [exact (He sig fs Hin) | exact (HT tr' sig fs Htr' Hin)].
Qed.

Lemma tset_no_kill_alt2 : forall A B, tset_no_kill A -> tset_no_kill B -> tset_no_kill (t_alt2 A B).
Proof. intros A B HA HB tr sig fs [H|H] Hin; [exact (HA _ _ _ H Hin) | exact (HB _ _ _ H Hin)]. Qed.

Lemma tset_no_kill_exit : forall code fs, tset_no_kill (t_exit code fs).
Proof.
  intros code fs. unfold t_exit. apply tset_no_kill_emit; [| exact tset_no_kill_nil].
  intros sig fs' [H | []]. discriminate H.
Qed.

Lemma W_no_kill : forall ch s sig fs, ~ In (KillEv sig fs) (W ch s).
Proof.
  intros ch s sig fs Hin. unfold W in Hin. apply in_map_iff in Hin. destruct Hin as (b & Hb & _). discriminate Hb.
Qed.

Lemma tset_no_kill_die : forall msg fs, tset_no_kill (t_die msg fs).
Proof. intros. unfold t_die. apply tset_no_kill_emit; [apply W_no_kill | apply tset_no_kill_exit]. Qed.

Ltac nokill_step :=
  lazymatch goal with
  | |- tset_no_kill (t_die _ _) => apply tset_no_kill_die
  | |- tset_no_kill (t_exit _ _) => apply tset_no_kill_exit
  | |- tset_no_kill (t_alt2 _ _) => apply tset_no_kill_alt2
  | |- tset_no_kill (t_emit _ _) => apply tset_no_kill_emit; [apply W_no_kill|]
  | |- tset_no_kill (if ?b then _ else _) => destruct b
  | |- tset_no_kill (match ?n with O => _ | S _ => _ end) => destruct n
  | |- tset_no_kill (match ?l with nil => _ | _ :: _ => _ end) => destruct l
  | |- tset_no_kill (match ?o with Some _ => _ | None => _ end) => destruct o
  | |- tset_no_kill (let x := _ in _) => cbv zeta
  end.

Lemma t_body_no_kill : forall data fs, tset_no_kill (t_body data fs).
Proof. intros data fs. unfold t_body. repeat nokill_step. Qed.

Lemma spec_no_kill : forall argv fs, tset_no_kill (spec argv fs).
Proof.
  intros argv fs. unfold spec, t_opened, t_opened_dir.
  repeat (nokill_step || apply t_body_no_kill).
Qed.
