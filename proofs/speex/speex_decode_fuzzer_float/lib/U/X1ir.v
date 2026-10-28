(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m5 X1le X1kx X1lp X1lu X1il X1ip.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r3 X1r4.

Lemma rtop_known_indep : forall (s s' : PState) (p : bptr), rtop_known s p -> rtop_known s' p.
Proof. intros s s' p H. exact H. Qed.

Lemma ogg_realloc_of_rrealloc {RCEIL : RunCeiling} : rrealloc_stmt -> ogg_realloc_stmt rtop_known.
Proof.
intros H. unfold ogg_realloc_stmt. intros.
unfold rrealloc_stmt, rrealloc_stmt_at in H. unfold A_realloc.
eapply H; try eassumption.
Qed.

Theorem ogg_HR {RCEIL : RunCeiling} : ogg_realloc_stmt rtop_known.
Proof. exact (ogg_realloc_of_rrealloc rrealloc_spec). Qed.

Definition ogg_HM {RCEIL : RunCeiling} : rmalloc_stmt := rmalloc_spec.
Definition ogg_HF {RCEIL : RunCeiling} : rfree_stmt := rfree_spec_proof.
