(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl Prog.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Malloc Require Import MallocRep MallocTree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Malloc Require Export MallocBlocks.
Import ListNotations.
Open Scope Z_scope.

Definition HINV_from (resv : list (Z * Z)) (st : mstate) (pbrk : Z) (LB : list block) : Prop :=
  brk_link st pbrk /\ AREACH_from resv st LB.

Lemma HINV_from_init : forall resv ceil pbrk, ceil <= alloc_ceiling_max -> HINV_from resv (minit 0 resv ceil) pbrk [].
Proof. intros. split; [exact I | apply areach_init; assumption]. Qed.

Lemma brk_link_ps_iff : forall st s, brk_link_ps st s <-> brk_link st (ps_brk s).
Proof. intros st s. unfold brk_link_ps, brk_link. destruct (c_brk (ctx st)); LiaTuning.ctauto. Qed.