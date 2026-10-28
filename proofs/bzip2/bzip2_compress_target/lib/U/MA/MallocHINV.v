(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Prog.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import MallocRep MallocTree.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Export MallocBlocks.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
Definition HINV_from (resv : list (Z * Z)) (st : mstate) (pbrk : Z) (LB : list block) : Prop :=
  brk_link st pbrk /\ AREACH_from resv st LB.
End ACeilS1.

Notation HINV := (HINV_from agent_reserved).
Section ACeilS2. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma brk_link_ps_iff : forall st s, brk_link_ps st s <-> brk_link st (ps_brk s).
Proof. intros st s. unfold brk_link_ps, brk_link. destruct (c_brk (ctx st)); tauto. Qed.

End ACeilS2.
