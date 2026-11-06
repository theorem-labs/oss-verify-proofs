(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import String Ascii ZArith Bool List Lia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint dec_digits_n (fuel : nat) (n : Z) (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S f => if n <? 10 then (48 + n) :: acc
           else dec_digits_n f (n / 10) ((48 + n mod 10) :: acc)
  end.
Definition Zdecimal (n : Z) : list Z := dec_digits_n 64 n [].

(* [comment removed for export] *)
Definition HEX_SIZE (len : Z) : Z := (len + 1) * 2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive tevent : Type :=
| TMalloc (n : Z) (r : option nat)
| TFree (p : option nat)
| TStderr (bytes : list Z)
| TStdout (bytes : list Z)
| TMsgStore (bytes : list Z)
| TReturn (rc : Z)
| TUnreachable.

(* [comment removed for export] *)
Record target_ops (M : Type -> Type) (ptr : Type) : Type := mkOps {
  ret : forall A : Type, A -> M A;
  bind : forall A B : Type, M A -> (A -> M B) -> M B;
  unreachable : forall A : Type, M A;
  lib_malloc : Z -> M (option ptr);          (* [comment removed for export] *)
  lib_free : option ptr -> M unit;           (* [comment removed for export] *)
  out_stderr : list Z -> M unit;             (* [comment removed for export] *)
  out_stdout : list Z -> M unit;             (* [comment removed for export] *)
  msg_store : list Z -> M unit               (* [comment removed for export] *)
}.
Arguments mkOps {M ptr}.
Arguments ret {M ptr} _ {A}.
Arguments bind {M ptr} _ {A B}.
Arguments unreachable {M ptr} _ {A}.
Arguments lib_malloc {M ptr}.
Arguments lib_free {M ptr}.
Arguments out_stderr {M ptr}.
Arguments out_stdout {M ptr}.
Arguments msg_store {M ptr}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Target.
Context {M : Type -> Type} {ptr : Type}.
Variable ops : target_ops M ptr.
Variable d : list Z.        (* [comment removed for export] *)

Local Notation "x <- m ;; k" := (bind ops m (fun x => k)) (at level 61, m at next level, right associativity).
Local Notation "m ;;; k" := (bind ops m (fun _ => k)) (at level 61, right associativity).

(* [comment removed for export] *)
Definition fuzz_one : M Z :=
  r <- lib_malloc ops (HEX_SIZE (zlength d)) ;;
  lib_free ops r ;;;
  ret ops 0.

(* [comment removed for export] *)
Fixpoint run_calls (n : nat) (rc : Z) : M Z :=
  match n with
  | O => ret ops rc
  | S n' =>
      rc' <- fuzz_one ;;
      out_stdout ops (Zdecimal rc' ++ [10]) ;;;       (* [comment removed for export] *)
      run_calls n' rc'
  end.

(* [comment removed for export] *)
Definition target_run (cfg : list Z) : M Z :=
  let c := match cfg with [] => 0 | b :: _ => b end in       (* [comment removed for export] *)
  let calls := Z.to_nat (Z.land c 3 + 1) in
  let plen := zlength d in
  (* [comment removed for export] *)
  a <- (if plen =? 0 then ret ops (Some None)
        else r <- lib_malloc ops plen ;;
             ret ops (match r with None => None | Some p => Some (Some p) end)) ;;
  match a with
  | None => ret ops 2                                          (* [comment removed for export] *)
  | Some owned =>
      rc <- run_calls calls 0 ;;
      lib_free ops owned ;;;                                   (* [comment removed for export] *)
      ret ops (if rc =? 0 then 0 else 1)
  end.

End Target.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Module HexRun.

Inductive ttree (A : Type) : Type :=
| TRet (a : A)
| TUnr
| TEv (e : tevent) (k : ttree A)
| TMallocQ (n : Z) (k : option nat -> ttree A).
Arguments TRet {A}.
Arguments TUnr {A}.
Arguments TEv {A}.
Arguments TMallocQ {A}.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

End HexRun.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Module HexModelTests.
Import HexRun.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

End HexModelTests.
