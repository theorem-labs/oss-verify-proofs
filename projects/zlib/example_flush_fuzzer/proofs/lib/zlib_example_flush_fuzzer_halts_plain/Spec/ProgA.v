(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Spec Require Import Prelim Monad Stdio Adapter Driver.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Record AAlloc : Type := mkAAlloc {
  ASt : Type;
  aptr : Type;
  amalloc : Z -> Monad.M ASt (option aptr);
  afree : aptr -> Monad.M ASt unit;
  aannot : aptr -> Z -> Z -> Z -> Monad.M ASt unit;
  aptr_addr : ASt -> aptr -> Z;
  afresh : ASt -> ASt -> aptr -> bool;
  a_so : ASt -> stdout_st;
  a_set_so : stdout_st -> ASt -> ASt
}.


Section ProgA.
Variable A : AAlloc.
Local Notation MA := (Monad.M (ASt A)).

Definition ioA : IOStyle (ASt A) := io_S (a_so A) (a_set_so A).

Definition alloc_initA : Z -> MA unit := Adapter.target_alloc_init.
Definition alloc_countA : MA Z := Adapter.target_alloc_count.

End ProgA.
