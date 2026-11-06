(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import RunConst.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AExit F_stdio_exit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Theorem stdio_exit_ghost : stdio_exit_spec_stmt2 (St := stdout_st) (fun so => so) (fun so _ => so).
Proof. apply stdio_exit_proof; intros; reflexivity. Qed.
End CANSEC1.
