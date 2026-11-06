(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AMain_final AHarnessM_closedI.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require AM_lambda AM_harness.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma lambda_thm_I : lambda_thm_type.
Proof. exact (fun rc => @AM_lambda.lambda_proof rc). Qed.

Lemma harness_thm_I : harness_thm_type.
Proof. exact (fun rc => @AM_harness.fuzz_oneU_proof rc). Qed.

Theorem asan_client_closed : asan_client_stmt.
Proof. exact (asan_client_of lambda_thm_I harness_thm_I). Qed.
