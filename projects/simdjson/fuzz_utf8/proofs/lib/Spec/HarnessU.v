(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad.
Import ListNotations.
Open Scope Z_scope.
Open Scope mspec_scope.

Section HarnessU.
Context {St ptr : Type}.
Variable raw_malloc : Z -> M St (option ptr).      (* [comment removed for export] *)
Variable raw_free : ptr -> M St unit.              (* [comment removed for export] *)
Variable new_handler : M St Empty_set.             (* [comment removed for export] *)
Variable cl_get : St -> option ptr.                (* [comment removed for export] *)
Variable cl_set : option ptr -> St -> St.

(* [comment removed for export] *)
Definition opnew (sz : Z) : M St ptr :=
  let sz' := if sz =? 0 then 1 else sz in
  r <- raw_malloc sz' ;;
  match r with
  | Some p => mret p
  | None => e <- new_handler ;; match (e : Empty_set) with end
  end.
Definition opdelete (p : ptr) : M St unit := raw_free p.

(* [comment removed for export] *)
Definition CLIENT_VEC_BYTES : Z := 8.

(* [comment removed for export] *)
Definition client_init : M St unit :=
  s <- mget ;;
  match cl_get s with
  | Some _ => mret tt
  | None => p <- opnew CLIENT_VEC_BYTES ;; mupd (cl_set (Some p))
  end.

(* [comment removed for export] *)
Definition fuzz_one (data : list Z) : M St Z := client_init ;;; mret 0.

(* [comment removed for export] *)
Definition client_exit : M St unit :=
  s <- mget ;;
  match cl_get s with
  | Some p => opdelete p ;;; mupd (cl_set None)
  | None => mret tt
  end.

(* [comment removed for export] *)
Lemma fuzz_one_later : forall data s p, cl_get s = Some p -> fuzz_one data s = Ret (ITree.Exc.Ok (0, s)).
Proof. intros data s p H. unfold fuzz_one, client_init, mbind, mget, mret. cbn. rewrite H. reflexivity. Qed.

Lemma fuzz_one_first : forall data s, cl_get s = None ->
  fuzz_one data s = ((p <- opnew CLIENT_VEC_BYTES ;; mupd (cl_set (Some p))) ;;; mret 0) s.
Proof. intros data s H. unfold fuzz_one, client_init, mbind, mget. cbn. rewrite H. reflexivity. Qed.

Lemma client_exit_none : forall s, cl_get s = None -> client_exit s = Ret (ITree.Exc.Ok (tt, s)).
Proof. intros s H. unfold client_exit, mbind, mget, mret. cbn. rewrite H. reflexivity. Qed.
End HarnessU.
