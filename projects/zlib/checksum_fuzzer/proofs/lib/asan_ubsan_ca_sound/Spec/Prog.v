(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode Image InitMem.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Spec Require Import Prelim Monad STree Malloc Stdio Harness Adapter Driver.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Spec Require Export PState.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Malloc Require Export ProgDeps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.


Local Notation MP := (Monad.M PState).

Definition io : IOStyle PState := io_S ps_so set_so_ps.

Definition fuzz_one : list Z -> MP Z := Harness.fuzz_one.
Definition run (cfg : Z) (payload : list Z) : MP Z :=
  Adapter.target_run raw_malloc raw_free fuzz_one (io_emit io) cfg payload.
Definition alloc_init : Z -> MP unit := Adapter.target_alloc_init.
Definition alloc_count : MP Z := Adapter.target_alloc_count.

Definition startup : MP unit := _ <- msys NSetTid dec_set_tid ;; mret tt.

Definition prog_with (rs : Z) (argv : list (list Z)) : MP Empty_set :=
  startup ;;;
  code <- main_model io raw_malloc raw_free rs alloc_init run alloc_count argv ;;
  exit_model io code.

Definition argv_Z (argv : list (list byte)) : list (list Z) := map (map bv_unsigned) argv.

Definition prog_itree (segs : list Segment) (rs : Z) (argv : list (list byte)) (atop : Z) : itree node (exc unit) :=
  ebind (prog_with rs (argv_Z argv) (ps_init (reservedZ segs) atop))
        (fun p => match fst p : Empty_set with end).

Definition prog (segs : list Segment) (rs : Z) (inp : ProcInput) (en : ExecEntry) : itree node (exc unit) :=
  prog_itree segs rs (in_argv inp) (entry_atop en).
