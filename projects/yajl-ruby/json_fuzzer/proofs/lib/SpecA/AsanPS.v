(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanFakeStack.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Record aps := mkAPS {
  aps_env : aenv;
  aps_alloc : astate;
  aps_fs : fsstate;
  aps_fsbase : Z;
  aps_so : stdout_st;
  aps_errno : Z;
  aps_initialized : Z;
  aps_credit : Z
}.

Definition aps_set_alloc (a : astate) (p : aps) : aps :=
  mkAPS (aps_env p) a (aps_fs p) (aps_fsbase p) (aps_so p) (aps_errno p) (aps_initialized p) (aps_credit p).
Definition aps_set_fs (f : fsstate) (p : aps) : aps :=
  mkAPS (aps_env p) (aps_alloc p) f (aps_fsbase p) (aps_so p) (aps_errno p) (aps_initialized p) (aps_credit p).
Definition aps_set_so (so : stdout_st) (p : aps) : aps :=
  mkAPS (aps_env p) (aps_alloc p) (aps_fs p) (aps_fsbase p) so (aps_errno p) (aps_initialized p) (aps_credit p).
Definition aps_set_errno (e : Z) (p : aps) : aps :=
  mkAPS (aps_env p) (aps_alloc p) (aps_fs p) (aps_fsbase p) (aps_so p) e (aps_initialized p) (aps_credit p).
Definition aps_set_initialized (v : Z) (p : aps) : aps :=
  mkAPS (aps_env p) (aps_alloc p) (aps_fs p) (aps_fsbase p) (aps_so p) (aps_errno p) v (aps_credit p).
Definition aps_set_credit (v : Z) (p : aps) : aps :=
  mkAPS (aps_env p) (aps_alloc p) (aps_fs p) (aps_fsbase p) (aps_so p) (aps_errno p) (aps_initialized p) v.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kInitialCredit : Z := 120000000.   (* [comment removed for export] *)
Definition aps_init (E : aenv) (fsbase : Z) : aps :=
  mkAPS E (astate0 E) fsstate0 fsbase stdout_init 0 0 kInitialCredit.
End RC__1.
