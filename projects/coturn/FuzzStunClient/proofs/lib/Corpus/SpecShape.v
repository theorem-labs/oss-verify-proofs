(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from projects/yajl-ruby/json_fuzzer/proofs/lib/Top/HaltsSpec.v at commit
   c395a1e0dfa, lines 23-58 (ev_ok_W, shape_ok_die, shape_ok_body, shape_ok_opened, shape_ok_opened_dir and
   shape_ok_spec), restated for this harness's Spec.spec: the exit-code list halts_codes becomes Corpus.HaltsFO's
   codes02, ev_ok_W becomes trace_ok_map_write plus shape_ok_emit_W over this tree's Common.ShapeAlg trace_ok, and the
   per-branch case analysis (shape_ok_zero_lines, shape_ok_exit_0_or_2, the spec_shape_step tactic) follows coturn's
   own t_body/t_opened/t_opened_dir rather than json_fuzzer's; yajl-ruby's spec_exits_in is not copied. *)
(* The exit statuses of the driver specification.

   [Spec.spec] is the trace set that both the plain and the UBSan build of this fuzz target realize
   ([BaseUbsan.ref_spec_stmt] and [BaseUbsan.ub_spec_stmt]).  Every branch of it ends in [t_exit (exit_code 0)] or
   [t_exit (exit_code 2)], and nothing in it is a [KillEv], so it is [shape_ok codes02] in the sense of
   [Corpus.HaltsFO].  That is the only fact about the specification the two halts proofs need. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Spec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Corpus Require Import HaltsFO.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* A run of writes on one descriptor carries no exit and no kill. *)
Lemma trace_ok_map_write : forall S ch bs, trace_ok S (map (WriteEv ch) bs).
Proof.
  intros S ch bs. unfold trace_ok. induction bs as [|b bs IH].
  - cbn [map]. constructor.
  - cbn [map]. constructor; [exact I | exact IH].
Qed.

Lemma shape_ok_emit_W : forall S ch bs T, shape_ok S T -> shape_ok S (t_emit (W ch bs) T).
Proof.
  intros S ch bs T HT. unfold W. apply shape_ok_emit; [apply trace_ok_map_write | exact HT].
Qed.

Lemma shape_ok_die : forall msg fs, shape_ok codes02 (t_die msg fs).
Proof.
  intros msg fs. unfold t_die. apply shape_ok_emit_W. apply shape_ok_exit. exact in_codes02_2.
Qed.

Lemma shape_ok_zero_lines : forall n fs,
  shape_ok codes02 (t_emit (W 1 (zero_lines n)) (t_exit (exit_code 0) fs)).
Proof.
  intros n fs. apply shape_ok_emit_W. apply shape_ok_exit. exact in_codes02_0.
Qed.

Lemma shape_ok_exit_0_or_2 : forall (b : bool) fs,
  shape_ok codes02 (t_exit (exit_code (if b then 0 else 2)) fs).
Proof.
  intros [] fs; apply shape_ok_exit; [exact in_codes02_0 | exact in_codes02_2].
Qed.

Ltac spec_shape_step :=
  first
    [ apply shape_ok_die
    | apply shape_ok_zero_lines
    | apply shape_ok_exit_0_or_2
    | apply shape_ok_alt2
    | match goal with
      | |- shape_ok _ (if ?b then _ else _) => destruct b
      | |- shape_ok _ (match ?n with O => _ | S _ => _ end) => destruct n
      | |- shape_ok _ (match ?o with Some _ => _ | None => _ end) => destruct o
      end ].

Lemma shape_ok_body : forall data fs, shape_ok codes02 (t_body data fs).
Proof.
  intros data fs. unfold t_body. cbv zeta. repeat spec_shape_step.
Qed.

Lemma shape_ok_opened : forall data fs, shape_ok codes02 (t_opened data fs).
Proof.
  intros data fs. unfold t_opened.
  apply shape_ok_alt2; [apply shape_ok_die | apply shape_ok_body].
Qed.

Lemma shape_ok_opened_dir : forall path fs, shape_ok codes02 (t_opened_dir path fs).
Proof.
  intros path fs. unfold t_opened_dir. apply shape_ok_alt2; apply shape_ok_die.
Qed.

(* The specification's exits are 0 and 2, whatever the argument vector and the file system. *)
Theorem shape_ok_spec : forall argv fs, shape_ok codes02 (spec argv fs).
Proof.
  intros argv fs. destruct argv as [|a0 [|path [|x l]]]; unfold spec; cbv beta iota zeta;
    repeat first
      [ apply shape_ok_opened_dir
      | apply shape_ok_opened
      | spec_shape_step ].
Qed.
