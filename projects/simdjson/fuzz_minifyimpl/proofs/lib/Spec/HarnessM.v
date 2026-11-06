(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Definition minify_step (st : bool * bool) (c : Z) : bool * bool :=
  let '(ne, q) := st in (negb ne || negb (c =? 92), xorb q ((c =? 34) && ne)).
Definition unclosed (data : list Z) : bool := snd (fold_left minify_step data (true, false)).

Lemma unclosed_nil : unclosed [] = false. Proof. reflexivity. Qed.

Section HarnessM.
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
Definition odelete (b : option ptr) : M St unit := match b with Some p => opdelete p | None => mret tt end.

(* [comment removed for export] *)
Definition CLIENT_VEC_BYTES : Z := 8.
(* [comment removed for export] *)
Definition ERRMSG_LEN : Z := 54.
Definition ERRSTR_BYTES : Z := 56.

(* [comment removed for export] *)
Definition client_init : M St unit :=
  s <- mget ;;
  match cl_get s with
  | Some _ => mret tt
  | None => p <- opnew CLIENT_VEC_BYTES ;; mupd (cl_set (Some p))
  end.

(* [comment removed for export] *)
Definition minify_call (data : list Z) : M St unit :=
  let n := Z.of_nat (length data) in
  b <- (if n =? 0 then mret None else p <- opnew n ;; mret (Some p)) ;;
  if unclosed data then
    t <- opnew ERRSTR_BYTES ;;
    b' <- (if ERRMSG_LEN <=? n then mret b else odelete b ;;; p' <- opnew ERRMSG_LEN ;; mret (Some p')) ;;
    opdelete t ;;;
    odelete b'
  else odelete b.

(* [comment removed for export] *)
Definition fuzz_one (data : list Z) : M St Z := client_init ;;; minify_call data ;;; mret 0.

(* [comment removed for export] *)
Definition client_exit : M St unit :=
  s <- mget ;;
  match cl_get s with
  | Some p => opdelete p ;;; mupd (cl_set None)
  | None => mret tt
  end.

(* [comment removed for export] *)
Lemma minify_call_nil : minify_call [] = mret tt.
Proof. unfold minify_call. cbn. unfold mbind, mret, odelete. reflexivity. Qed.

Lemma client_exit_none : forall s, cl_get s = None -> client_exit s = Ret (ITree.Exc.Ok (tt, s)).
Proof. intros s H. unfold client_exit, mbind, mget, mret. cbn. rewrite H. reflexivity. Qed.
End HarnessM.
