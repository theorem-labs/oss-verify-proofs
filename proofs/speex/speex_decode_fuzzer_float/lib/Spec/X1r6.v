(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1bz X1bo X1bs X1c2 X1bn.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1ra X1qu X1ri X1r3
X1nt X1rh X1re X1qz X1rg X1od X1rm X1o8.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Export X1r4.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Notation MP := (X1qx.M PState).

Section IO.
Definition io_diag : diag_msg -> MP unit := s_diag.
Definition io_emit : Z -> MP unit := s_emit ps_so set_so_ps.
Definition io_notify : list Z -> MP unit := s_notify.
Definition io_warning : list Z -> MP unit := s_warning.
Definition io_exit : Z -> MP Empty_set := stdio_exit_model ps_so set_so_ps.
End IO.

Definition fuzz_one (payload : list Z) : MP Z :=
LLVMFuzzerTestOneInput raw_malloc raw_calloc raw_realloc raw_free io_notify io_warning
bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M payload.

Definition run (cfg : Z) (payload : list Z) : MP Z :=
target_run raw_malloc raw_free io_emit fuzz_one cfg payload.

Definition startup : MP unit := _ <- msys NSetTid dec_set_tid ;; mret tt.

Definition prog_with (rstage : Z) (argv : list (list Z)) : MP Empty_set :=
startup ;;;
code <- main_model io_diag raw_malloc raw_free rstage
(target_alloc_init (St:=PState)) run (target_alloc_count (St:=PState)) argv ;;
io_exit code.

Definition prog (segs : list Segment) (rstage ceil : Z) (argv : list (list byte)) : itree node (exc unit) :=
ebind (prog_with rstage (argv_Z argv) (ps_init ceil (reservedZ segs)))
(fun p => match fst p : Empty_set with end).

Definition prog_plain := prog.
Definition prog_ubsan := prog.

Definition RSTAGE_plain : Z := 0x35e39.
Definition RSTAGE_ubsan : Z := 0x3d349.
