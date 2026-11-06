(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio HarnessM Adapter Driver ProgA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Record ZSt := mkZ {
  z_so : stdout_st;          (* [comment removed for export] *)
  z_cl : option unit         (* [comment removed for export] *)
}.
Definition z_set_so (v : stdout_st) (s : ZSt) : ZSt := mkZ v (z_cl s).
Definition z_set_cl (v : option unit) (s : ZSt) : ZSt := mkZ (z_so s) v.

Definition zmalloc (n : Z) : Monad.M ZSt (option unit) := mret (Some tt).
Definition zfree (p : unit) : Monad.M ZSt unit := mret tt.
Definition zannot (p : unit) (cap old new : Z) : Monad.M ZSt unit := mret tt.

Definition AAllocZ : AAlloc := mkAAlloc ZSt unit zmalloc zfree zannot (fun _ _ => 0) z_so z_set_so z_cl z_set_cl.

Definition sZ_init : ZSt := mkZ stdout_init None.

Definition progZ_tree (rs : Z) (argv : list (list Z)) : itree node (exc unit) := progA_tree AAllocZ sZ_init rs argv.

Lemma z_get_set : forall v s, z_so (z_set_so v s) = v. Proof. reflexivity. Qed.
Lemma z_set_set : forall v w s, z_set_so v (z_set_so w s) = z_set_so v s. Proof. reflexivity. Qed.
Lemma z_set_get : forall s, z_set_so (z_so s) s = s. Proof. intros [so cl]; reflexivity. Qed.
Lemma z_cl_so : forall v s, z_cl (z_set_so v s) = z_cl s. Proof. reflexivity. Qed.
Lemma z_so_cl : forall v s, z_so (z_set_cl v s) = z_so s. Proof. reflexivity. Qed.
Lemma z_cl_get_set : forall v s, z_cl (z_set_cl v s) = v. Proof. reflexivity. Qed.
