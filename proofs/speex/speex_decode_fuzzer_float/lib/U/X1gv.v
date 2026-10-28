(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r3 X1r4 X1re.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ik X1m5 X1m6 X1le X1kx X1ec X1lu X1ir X1ip X1is X1iv X1fr X1ep X1gf X1g3 X1g5 X1ee X1gb X1h7 X1go X1gp X1hg X1ha.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.

Lemma bits_realloc_closed {RCEIL : RunCeiling} : bits_realloc_stmt rtop_known.
Proof. exact rrealloc_spec. Qed.

Lemma ogg_stream_init_closed {RCEIL : RunCeiling} : ogg_stream_init_stmt2.
Proof. exact (ogg_stream_init_spec rmalloc_spec rfree_spec_proof). Qed.

Lemma ogg_stream_pagein_closed {RCEIL : RunCeiling} : ogg_stream_pagein_stmt2.
Proof.
unfold ogg_stream_pagein_stmt2. intros.
eapply (ogg_stream_pagein_spec rtop_known rtop_known_indep ogg_HR rfree_spec_proof); eassumption.
Qed.

Section DEC.
Context {RCEIL : RunCeiling}.
Variable dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop.
Hypothesis DRF : dec_rep_frame_stmt dec_rep.
Hypothesis DINIT : rspx_decoder_init_stmt dec_rep.
Hypothesis DCTL : rspx_decoder_ctl_stmt dec_rep.
Hypothesis DDESTROY : rspx_decoder_destroy_stmt dec_rep.
Hypothesis DECODE : rspx_decode_stmt dec_rep.

#[using="dec_rep DRF DINIT DCTL DDESTROY DECODE"] Theorem harness_closed : harness_stmt.
Proof.
exact (harness_proof dec_rep DRF DINIT DCTL DDESTROY DECODE
decode_stereo_proof speex_packet_to_header_closed
fwritex_stderr_proof stdio_write_flush_proof
bits_realloc_closed rcalloc_spec rmalloc_spec rfree_spec_proof ogg_HR
RHEAP_frame_proof RHEAP_block_range_proof RHEAP_blocks_nodup_proof RHEAP_blocks_disjoint_proof
RHEAP_top_known_proof ogg_stream_init_closed ogg_stream_pagein_closed).
Qed.
End DEC.
