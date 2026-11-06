(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode Image InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad STree Malloc Stdio Harness Adapter Driver.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Export PState.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Malloc Require Export ProgDeps.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)

Local Notation MP := (Monad.M PState).

(* [comment removed for export] *)
Definition io : IOStyle PState := io_S ps_so set_so_ps.

(* [comment removed for export] *)
Definition new_handler : MP Empty_set := munr.

(* [comment removed for export] *)
Definition fuzz_one : list Z -> MP Z := Harness.fuzz_one raw_malloc raw_free new_handler.
Definition run (cfg : Z) (payload : list Z) : MP Z :=
  Adapter.target_run raw_malloc raw_free fuzz_one (io_emit io) cfg payload.
Definition alloc_init : Z -> MP unit := Adapter.target_alloc_init.
Definition alloc_count : MP Z := Adapter.target_alloc_count.

(* [comment removed for export] *)
Definition startup : MP unit := _ <- msys NSetTid dec_set_tid ;; mret tt.

(* [comment removed for export] *)
Definition prog_with (rs : Z) (argv : list (list Z)) : MP Empty_set :=
  startup ;;;
  code <- main_model io raw_malloc raw_free rs alloc_init run alloc_count argv ;;
  exit_model io code.

(* [comment removed for export] *)
Definition argv_Z (argv : list (list byte)) : list (list Z) := map (map bv_unsigned) argv.

(* [comment removed for export] *)
Definition prog_itree (segs : list Segment) (rs : Z) (argv : list (list byte)) (atop : Z) : itree node (exc unit) :=
  ebind (prog_with rs (argv_Z argv) (ps_init (reservedZ segs) atop))
        (fun p => match fst p : Empty_set with end).

(* [comment removed for export] *)
Definition prog (segs : list Segment) (rs : Z) (inp : ProcInput) (en : ExecEntry) : itree node (exc unit) :=
  prog_itree segs rs (in_argv inp) (entry_atop en).
