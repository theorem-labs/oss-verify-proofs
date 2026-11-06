(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Monad MSafe MSil STree Malloc MallocCtrl RawAlloc Realloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocOracle.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope mspec_scope.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition raw_realloc (o : mem) (st : mstate) (p : aptr) (n : Z) : Monad.M PState (mstate * optr) :=
  r <- xmembed (xmrun o (realloc st (Some p) n)) ;;
  mupd (set_m (strip (fst (snd r)))) ;;; mret (snd r).

(* [comment removed for export] *)
Lemma tmm_raw_realloc o st p n s : tmm (raw_realloc o st p n s).
Proof.
  unfold raw_realloc. apply tmm_mbind.
  - generalize (xmrun o (realloc st (Some p) n)) as t. intros t. revert s.
    induction t as [r|e k IH]; intros s; cbn [xmembed]; [apply tmm_mret|].
    apply tmm_mbind; [| intros; apply IH].
    destruct e as [e'|a ol nl fl]; cbn [xev_step].
    + destruct e'; cbn [ev_step];
        repeat (first [ apply tmm_mif | apply tmm_mbind | apply tmm_msys | apply tmm_mret | apply tmm_munr | apply tmm_mget | apply tmm_mupd | exact I ]; intros);
        try (match goal with |- tmm (match ?a with _ => _ end _) => destruct a end;
             repeat (first [ apply tmm_mbind | apply tmm_mret | apply tmm_mupd | exact I ]; intros)).
    + apply tmm_mbind; [apply tmm_msys; exact I| intros; apply tmm_mret].
  - intros r s'. apply tmm_mbind; [apply tmm_mupd| intros; apply tmm_mret].
Qed.
End RC__1.
