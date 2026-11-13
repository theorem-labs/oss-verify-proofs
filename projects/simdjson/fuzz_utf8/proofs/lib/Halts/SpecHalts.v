(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from projects/fast_float/from_chars/proofs/lib/SpecHalts.v at commit c395a1e0dfa (its EXS and NK predicates, their closure lemmas and the two theorems built from them, lines 15-140), restated for skcms/iccprofile_info's Info.Spec.spec and Info.ShapeAlg trace algebra; the case analysis follows this harness's spec, not from_chars's. *)
(* Modified by gabelogan195, 2026-11: made from projects/skcms/iccprofile_info/proofs/lib/Halts/SpecHalts.v at commit f92feaf8b7 (HALT_CODES, the EXS predicate and its closure lemmas), restated for simdjson/fuzz_utf8's Common.Spec.spec and Common.ShapeAlg trace algebra, whose case analysis it follows; the NK half is left out, because Common.SpecNoKill.spec_nokill already states it. *)
(** The exit statuses of the trace set that both halting proofs consume: every
    exit the set [Common.Spec.spec] admits carries status 0 or 2. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import ShapeAlg Spec.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(** The statuses [Statements.plain_halts] and its siblings allow, as
    [Core.Shapes.Exits.ok_or_refused] spells them. *)
Definition HALT_CODES : list word := [Z_to_bv 64 0; Z_to_bv 64 2].

Lemma in_code0 : In (exit_code 0) HALT_CODES. Proof. left. reflexivity. Qed.
Lemma in_code2 : In (exit_code 2) HALT_CODES. Proof. right. left. reflexivity. Qed.

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

Lemma exs_die : forall msg fs, EXS (t_die msg fs).
Proof.
  intros msg fs. unfold t_die. apply exs_emit; [| apply exs_exit; exact in_code2].
  intros code fs' Hin. exfalso. exact (exs_W _ _ _ _ Hin).
Qed.

Lemma exs_body : forall data fs, EXS (t_body data fs).
Proof.
  intros data fs. unfold t_body. cbv zeta.
  repeat (match goal with |- EXS (if ?b then _ else _) => destruct b end;
          [apply exs_die | ]).
  apply exs_emit; [| apply exs_exit; unfold lib_status; exact in_code0].
  intros code fs' Hin. exfalso. exact (exs_W _ _ _ _ Hin).
Qed.

Lemma exs_spec : forall argv fs0, EXS (spec argv fs0).
Proof.
  intros argv fs0. unfold spec.
  destruct argv as [|a0 [|path [|a2 r]]]; try apply exs_die.
  destruct (4096 <=? length path)%nat; [apply exs_die|].
  destruct (list_byte_eqb path []); [apply exs_die|].
  destruct (list_byte_eqb path dot_path);
    [apply exs_alt2; [apply exs_die | unfold t_opened_dir; apply exs_die]|].
  destruct (fs_lookup fs0 path) as [data|]; [| apply exs_die].
  apply exs_alt2; [apply exs_die | unfold t_opened; apply exs_body].
Qed.
