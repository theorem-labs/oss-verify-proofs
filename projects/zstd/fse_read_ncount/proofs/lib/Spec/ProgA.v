(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad Stdio Harness Adapter Driver.
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
a_so : ASt -> stdout_st;
a_set_so : stdout_st -> ASt -> ASt
}.
Section ProgA.
Variable A : AAlloc.
Local Notation MA := (Monad.M (ASt A)).
Definition ioA : IOStyle (ASt A) := io_S (a_so A) (a_set_so A).
Definition new_handlerA : MA Empty_set := munr.
Definition fuzz_oneA : list Z -> MA Z :=
Harness.fuzz_one (amalloc A) (afree A) new_handlerA.
Definition runA (cfg : Z) (payload : list Z) : MA Z :=
Adapter.target_run (amalloc A) (afree A) fuzz_oneA (io_emit ioA) cfg payload.
Definition alloc_initA : Z -> MA unit := Adapter.target_alloc_init.
Definition alloc_countA : MA Z := Adapter.target_alloc_count.
Definition progA_main (rs : Z) (argv : list (list Z)) : MA Empty_set :=
code <- main_model ioA (amalloc A) (afree A) rs alloc_initA runA alloc_countA argv ;;
exit_model ioA code.
Definition progA_tree (s0 : ASt A) (rs : Z) (argv : list (list Z)) : itree node (exc unit) :=
ebind (progA_main rs argv s0) (fun p => match fst p : Empty_set with end).
End ProgA.
