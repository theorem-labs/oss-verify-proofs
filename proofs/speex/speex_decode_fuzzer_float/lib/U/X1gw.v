(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r3 X1r4 X1re.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ik. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1n8 X1my X1nc X1nd X1h7 X1go X1gv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.

Section DEC.
Context {RCEIL : RunCeiling}.
Hypothesis DECODE : rspx_decode_stmt DECREP.

#[using="DECODE"] Theorem harness_closed_dec : harness_stmt.
Proof.
exact (harness_closed DECREP dec_rep_frame_proof rspx_decoder_init_proof rspx_decoder_ctl_proof rspx_decoder_destroy_proof DECODE).
Qed.
End DEC.
