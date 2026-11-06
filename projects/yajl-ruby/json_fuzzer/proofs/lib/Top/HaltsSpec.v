(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import LiaTuning.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import SpecT HaltsGen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

Definition halts_codes : list word := [Z_to_bv 64 0; Z_to_bv 64 2].

Lemma in_halts_codes_0 : In (exit_code 0) halts_codes.
Proof. left. reflexivity. Qed.

Lemma in_halts_codes_2 : In (exit_code 2) halts_codes.
Proof. right. left. reflexivity. Qed.

Lemma ev_ok_W : forall S ch s, Forall (ev_ok S) (W ch s).
Proof. intros S ch s. unfold W. apply ev_ok_writes. Qed.

Lemma shape_ok_die : forall msg fs, shape_ok halts_codes (t_die msg fs).
Proof.
  intros msg fs. unfold t_die.
  apply shape_ok_emit; [apply ev_ok_W | apply shape_ok_exit, in_halts_codes_2].
Qed.

Lemma shape_ok_body : forall data fs, shape_ok halts_codes (t_body data fs).
Proof.
  intros data fs. unfold t_body. cbv zeta.
  repeat match goal with
         | |- shape_ok _ (if ?b then _ else _) => destruct b
         end;
    try apply shape_ok_die.
  apply shape_ok_emit; [apply ev_ok_W | apply shape_ok_exit, in_halts_codes_0].
Qed.

Lemma shape_ok_opened : forall data fs, shape_ok halts_codes (t_opened data fs).
Proof. intros data fs. unfold t_opened. apply shape_ok_body. Qed.

Lemma shape_ok_opened_dir : forall path fs, shape_ok halts_codes (t_opened_dir path fs).
Proof. intros path fs. unfold t_opened_dir. apply shape_ok_die. Qed.

Theorem shape_ok_spec : forall argv fs, shape_ok halts_codes (spec argv fs).
Proof.
  intros argv fs. unfold spec.
  destruct argv as [| a0 [| path [| x l]]]; try apply shape_ok_die.
  repeat match goal with
         | |- shape_ok _ (if ?b then _ else _) => destruct b
         | |- shape_ok _ (match ?o with Some _ => _ | None => _ end) => destruct o
         | |- shape_ok _ (t_alt2 _ _) => apply shape_ok_alt2
         end;
    first [ apply shape_ok_die | apply shape_ok_opened | apply shape_ok_opened_dir ].
Qed.

Theorem spec_exits_in : forall argv fs, exits_in halts_codes (spec argv fs).
Proof. intros argv fs. apply shape_ok_exits_in, shape_ok_spec. Qed.
