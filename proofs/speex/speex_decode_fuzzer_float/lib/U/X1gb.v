(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bs X1c2.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qn X0px X0qp.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m5 X1m6 X1ec X1kx X1fr X1ep X1gf X1g3 X1g5 X1g2 X1go X1ga.
Import ListNotations.
Open Scope Z_scope.

Lemma p2h_notify_closed : bits_notify_stmt X1ri.s_notify stderr_wfile X1fl.ssp_cells P2H_STR_TOP.
Proof. exact (bits_notify_of_stdio fwritex_stderr_proof stdio_write_flush_proof). Qed.

Theorem speex_packet_to_header_closed {RCEIL : RunCeiling} : rspx_packet_to_header_stmt.
Proof.
apply speex_packet_to_header_proof.
- exact rcalloc_spec.
- exact rfree_spec_proof.
- exact p2h_notify_closed.
- exact RHEAP_frame_proof.
- exact RHEAP_block_range_proof.
- exact RHEAP_blocks_disjoint_proof.
- exact RHEAP_blocks_nodup_proof.
Qed.
