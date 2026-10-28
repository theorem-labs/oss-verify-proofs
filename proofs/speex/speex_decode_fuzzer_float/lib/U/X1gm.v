(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r3 X1r4 X1r6 X1ri X1re.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1fr X1ep X1gf X1ho X1hq X1n8 X1mc X1na X1n9 X1mx X1md X1h7 X1go X1gw.

Lemma nbdec_closed : nb_decode_stmtW.
Proof. exact (nb_decode_linked (ptr:=bptr) fwritex_stderr_proof stdio_write_flush_proof). Qed.

Lemma sbh_closed {RCEIL : RunCeiling} : forall k,
(forall d, (dec_depth d <= k)%nat -> rdec_at A_speex_decode_native d) ->
(forall d, (dec_depth d <= k)%nat -> rctl_at d) ->
sb_hyps k.
Proof. exact (sb_hyps_linked fwritex_stderr_proof stdio_write_flush_proof). Qed.

Theorem harness_proof_final : forall (RCEIL : RunCeiling), @harness_stmt RCEIL.
Proof. intros RCEIL. exact (harness_closed_dec (rspx_decode_proof nbdec_closed sb_decode_ok sbh_closed)). Qed.

Lemma harness_proof_modulo_sb {RCEIL : RunCeiling} : sb_decode_goal -> harness_stmt.
Proof. intros _. exact (harness_proof_final RCEIL). Qed.
