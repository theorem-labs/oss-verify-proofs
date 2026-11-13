(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from projects/fast_float/from_chars/proofs/lib/SpecHalts.v at commit c395a1e0dfa (its EXS and NK predicates, their closure lemmas and the two theorems built from them, lines 15-140), restated for skcms/iccprofile_info's Info.Spec.spec and Info.ShapeAlg trace algebra; the case analysis follows this harness's spec, not from_chars's. *)
(* Modified by gabelogan195, 2026-11: made from projects/skcms/iccprofile_info/proofs/lib/Halts/SpecHalts.v at commit f92feaf8b7 (HALT_CODES, in_code0, in_code2, the EXS predicate and its closure lemmas prefix_in, exs_emit, exs_nil, exs_exit, exs_alt2, exs_W and exs_die), restated over double-conversion/string_to_double_fuzzer's Spec and ShapeAlg; its NK half is left out, this folder's SpecNoKill.spec_no_kill serving instead; in_code_ite, exs_W_none, exs_step, exs_body and exs_spec are new, a case walk of this harness's spec in the manner of SpecNoKill's nokill_step. *)
(** The fact about the harness's trace set that a halting proof consumes
    besides [SpecNoKill.spec_no_kill]: every exit status it admits is 0 or
    2.  It is read straight off [Spec.spec]: the driver's refusals and the
    out-of-memory paths exit 2, a completed run exits 0, and the exit taken
    when the payload copy cannot be made is 0 in counting mode and 2
    otherwise. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ShapeAlg Spec.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(** The statuses [Statements.plain_halts] and its siblings allow, as
    [Core.Shapes.Exits.ok_or_refused] spells them. *)
Definition HALT_CODES : list word := [Z_to_bv 64 0; Z_to_bv 64 2].

Lemma in_code0 : In (exit_code 0) HALT_CODES. Proof. left. reflexivity. Qed.
Lemma in_code2 : In (exit_code 2) HALT_CODES. Proof. right. left. reflexivity. Qed.

Lemma in_code_ite : forall b : bool, In (exit_code (if b then 0%Z else 2%Z)) HALT_CODES.
Proof. intros [|]; [exact in_code0 | exact in_code2]. Qed.

(** ** Every exit event of the set carries an allowed status *)

Definition EXS (T : TSet) : Prop :=
  forall tr code fs, T tr -> In (ExitEv code fs) tr -> In code HALT_CODES.

Lemma prefix_in : forall {A} (l1 l2 : list A) x, is_prefix l1 l2 -> In x l1 -> In x l2.
Proof.
  intros A l1. induction l1 as [|a l1 IH]; intros l2 x H Hx; [destruct Hx|].
  destruct l2 as [|b l2]; [destruct H|]. destruct H as [-> H].
  destruct Hx as [->|Hx]; [left; reflexivity | right; exact (IH l2 x H Hx)].
Qed.

Lemma exs_emit : forall evs T,
  (forall code fs, In (ExitEv code fs) evs -> In code HALT_CODES) -> EXS T -> EXS (t_emit evs T).
Proof.
  intros evs T He HT tr code fs [Hp | (tr' & -> & Htr')] Hin.
  - exact (He code fs (prefix_in tr evs _ Hp Hin)).
  - apply in_app_iff in Hin as [Hin|Hin]; [exact (He code fs Hin) | exact (HT tr' code fs Htr' Hin)].
Qed.

Lemma exs_nil : EXS t_nil.
Proof. intros tr code fs -> Hin. destruct Hin. Qed.

Lemma exs_exit : forall c fs, In c HALT_CODES -> EXS (t_exit c fs).
Proof.
  intros c fs Hc. unfold t_exit. apply exs_emit; [|exact exs_nil].
  intros code fs' [H|[]]. injection H as <- _. exact Hc.
Qed.

Lemma exs_alt2 : forall A B, EXS A -> EXS B -> EXS (t_alt2 A B).
Proof. intros A B HA HB tr code fs [H|H]; [exact (HA tr code fs H) | exact (HB tr code fs H)]. Qed.

Lemma exs_W : forall ch s code fs, ~ In (ExitEv code fs) (W ch s).
Proof. intros ch s code fs Hin. unfold W in Hin. apply in_map_iff in Hin as (b & Hb & _). discriminate Hb. Qed.

Lemma exs_W_none : forall ch s code fs, In (ExitEv code fs) (W ch s) -> In code HALT_CODES.
Proof. intros ch s code fs Hin. exfalso. exact (exs_W ch s code fs Hin). Qed.

Lemma exs_die : forall msg fs, EXS (t_die msg fs).
Proof.
  intros msg fs. unfold t_die. apply exs_emit; [| apply exs_exit; exact in_code2].
  intros code fs' Hin. exfalso. exact (exs_W _ _ _ _ Hin).
Qed.

(** One step of the case walk: the shapes [Spec.spec] is built from, and the
    branchings it makes on the input. *)
Ltac exs_step :=
  lazymatch goal with
  | |- EXS (t_die _ _) => apply exs_die
  | |- EXS (t_exit (exit_code (if _ then _ else _)) _) => apply exs_exit; apply in_code_ite
  | |- EXS (t_exit _ _) => apply exs_exit; first [exact in_code0 | exact in_code2]
  | |- EXS (t_alt2 _ _) => apply exs_alt2
  | |- EXS (t_emit _ _) => apply exs_emit; [exact (exs_W_none _ _) |]
  | |- EXS (if ?b then _ else _) => destruct b
  | |- EXS (match ?n with O => _ | S _ => _ end) => destruct n
  | |- EXS (match ?l with nil => _ | _ :: _ => _ end) => destruct l
  | |- EXS (match ?o with Some _ => _ | None => _ end) => destruct o
  | |- EXS (let x := _ in _) => cbv zeta
  end.

Lemma exs_body : forall data fs, EXS (t_body data fs).
Proof. intros data fs. unfold t_body. repeat exs_step. Qed.

Lemma exs_spec : forall argv fs0, EXS (spec argv fs0).
Proof.
  intros argv fs0. unfold spec, t_opened, t_opened_dir.
  repeat (exs_step || apply exs_body).
Qed.
