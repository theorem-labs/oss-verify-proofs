(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3 X1r6 X1oc X1ri.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pv X0px X0qp.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ea X1fl X1jh X1fr X1ek.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1n8 X1ho X1hm X1hr X1hq X1f9 X1gd X1ef X1et X1f2 X1f4 X1fs X1fx X1mc X1mz.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.

Lemma nb_notify_mono : forall notify serr sspc T1 T2, T1 <= T2 ->
nb_notify_stmt notify serr sspc T2 -> nb_notify_stmt notify serr sspc T1.
Proof.
intros notify serr sspc T1 T2 LE H. unfold nb_notify_stmt in *. intros until canary.
intros Ha0 Ha1 sfH_; first [ sf_destruct 8%nat sfH_ as slack BY HF SLK LEN POS DJ GA | sf_fb; destruct sfH_ as (slack & BY & HF & SLK & LEN & POS & DJ & GA) ]. intros.
eapply H; try eassumption.
exists slack. repeat (split; [eassumption|]). destruct GA as [GA|GA]; [left; exact GA| right; lia].
Qed.

Lemma SB_STR_TOP_le : SB_STR_TOP <= NB_STR_TOP.
Proof. unfold SB_STR_TOP, NB_STR_TOP. lia. Qed.

Section Link.
Context {RCEIL : RunCeiling}.

Hypothesis FWE : fwritex_stderr_stmt.
Hypothesis FLS : stdio_write_flush_stmt.

#[using="FWE FLS"] Theorem sb_hyps_linked : forall k,
(forall d, (dec_depth d <= k)%nat -> rdec_at A_speex_decode_native d) ->
(forall d, (dec_depth d <= k)%nat -> rctl_at d) ->
sb_hyps k.
Proof.
intros k NATIVE CTL. constructor.
- exact NATIVE.
- exact CTL.
- intros d _. apply rctl_isave_all.
- exact lsp_unquant_high_proof.
- exact split_cb_shape_sign_unquant_proof.
- exact lsp_interpolate8_spec.
- exact lsp_to_lpc8_spec.
- exact iir_mem16_8_spec.
- exact compute_rms16_w_proof.
- exact signal_mul_w_proof.
- exact exp_proof.
- exact qmf_synth_proof.
- exact (sb_decode_lost_closed iir_mem16_8_spec).
- eapply nb_notify_mono; [apply SB_STR_TOP_le|]. exact (nb_notify_of_stdio FWE FLS).
- exact stderr_wfile_serr_frame.
- exact ssp_cells_sspc_frame.
Qed.
End Link.
