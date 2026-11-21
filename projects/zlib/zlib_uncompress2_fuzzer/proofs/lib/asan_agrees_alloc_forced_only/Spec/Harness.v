(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import Prelim Monad.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope mspec_scope.

Section Harness.
Context {St ptr : Type}.
Variable malloc : Z -> M St (option ptr).
Variable free : ptr -> M St unit.
Variable script : list Z -> list Z.

Fixpoint alloc_all (ns : list Z) (acc : list ptr) : M St (list ptr) :=
  match ns with
  | [] => mret acc
  | n :: ns' => r <- malloc n ;; match r with Some p => alloc_all ns' (p :: acc) | None => mret acc end
  end.

Fixpoint free_all (ps : list ptr) : M St unit :=
  match ps with
  | [] => mret tt
  | p :: ps' => free p ;;; free_all ps'
  end.

Definition fuzz_one (data : list Z) : M St Z :=
  ps <- alloc_all (script data) [] ;; free_all ps ;;; mret 0.

End Harness.
