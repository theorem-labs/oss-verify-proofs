(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import AMain_final AHarnessM_closedI.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require AU_first_M AAtexit_iface AM_lambda AM_harness.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma lambda_thm_I : lambda_thm_type.
Proof. exact (fun rc => @AM_lambda.lambda_proof rc). Qed.

Lemma harness_thm_I : harness_thm_type.
Proof.
  intros rc AI fflag rng_fs K IMG_CI SM3 FF FR LAM RFSM ONTA LSAN FLSAN.
  exact (@AM_harness.fuzz_oneU_proof rc AI fflag rng_fs K IMG_CI SM3 FF FR LAM RFSM
           (@AU_first_M.rsi_proof rc AI IMG_CI ONTA) AAtexit_iface.acxa_atexit_proof LSAN FLSAN).
Qed.

Theorem asan_client_closed : asan_client_stmt.
Proof. exact (asan_client_of lambda_thm_I harness_thm_I). Qed.
