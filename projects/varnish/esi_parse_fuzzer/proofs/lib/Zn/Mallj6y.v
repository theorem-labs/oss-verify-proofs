(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import MRep MRepAux MTree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Export Mall5lv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Definition HINV_from (resv : list (Z * Z)) (st : mstate) (pbrk : Z) (LB : list block) : Prop :=
  brk_link st pbrk /\ AREACH_from resv st LB.

End CEIL.
Notation HINV := (HINV_from p0_reserved).  (* [comment removed for export] *)

Section CEIL2.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Lemma HINV_from_init : forall resv pbrk, HINV_from resv (minit run_secret resv) pbrk [].
Proof. intros. split; [exact I | apply areach_init]. Qed.

Lemma HINV_init : forall pbrk, HINV (minit run_secret p0_reserved) pbrk [].
Proof. intros. apply HINV_from_init. Qed.

End CEIL2.

Lemma brk_link_ps_iff : forall st s, brk_link_ps st s <-> brk_link st (ps_brk s).
Proof. intros st s. unfold brk_link_ps, brk_link. destruct (c_brk (ctx st)); tauto. Qed.
