(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import ITree Nodes CTree.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import Prelim Monad CMonad Stdio Client Harness HarnessC Adapter AdapterC Driver DriverC ProgA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section ProgAC.
Variable A : AAlloc.
Local Notation MCA := (MC (ASt A)).

Definition fuzz_oneAC : list Z -> MCA Z := HarnessC.fuzz_one (amalloc A) (afree A) Client.CLIENT_PRE Client.CLIENT_OPT.
Definition runAC (cfg : Z) (payload : list Z) : MCA Z :=
  AdapterC.target_run (amalloc A) (afree A) fuzz_oneAC (io_emit (ioA A)) cfg payload.

Definition progA_mainC (rs : Z) (argv : list (list Z)) : MCA Empty_set :=
  cmbind (DriverC.main_model (ioA A) (amalloc A) (afree A) rs (alloc_initA A) runAC (alloc_countA A) argv) (fun code =>
  DriverC.exit_model (ioA A) code).

Definition progA_mainD (D : hist -> bool) (rs : Z) (argv : list (list Z)) : Monad.M (ASt A) Empty_set :=
  RES D [] (progA_mainC rs argv).
Definition progA_treeD (D : hist -> bool) (s0 : ASt A) (rs : Z) (argv : list (list Z)) : itree node (exc unit) :=
  ebind (progA_mainD D rs argv s0) (fun p => match fst p : Empty_set with end).

End ProgAC.
