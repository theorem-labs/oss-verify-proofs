(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Lib Require Import ITree Nodes CTree.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Spec Require Import Prelim Monad CMonad Stdio HarnessC Adapter AdapterC Driver DriverC ProgA.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import ExFlushIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section ProgAC.
Variable A : AAlloc.
Variable FM : flush_model.
Local Notation MCA := (MC (ASt A)).

Definition fuzz_oneAC : list Z -> MCA Z := HarnessC.fuzz_one FM (amalloc A) (afree A) (afresh A).
Definition runAC (cfg : Z) (payload : list Z) : MCA Z :=
  AdapterC.target_run (amalloc A) (afree A) fuzz_oneAC (io_emit (ioA A)) cfg payload.

Definition progA_mainC (rs : Z) (argv : list (list Z)) : MCA Empty_set :=
  cmbind (DriverC.main_model (ioA A) (amalloc A) (afree A) rs (alloc_initA A) runAC (alloc_countA A) argv) (fun code =>
  DriverC.exit_model (ioA A) code).

End ProgAC.
