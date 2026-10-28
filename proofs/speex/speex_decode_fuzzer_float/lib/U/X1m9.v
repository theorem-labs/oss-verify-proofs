(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1bs X1c2.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1ri X1o8 X1rm X1r3 X1r6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m5 X1ea X1m8 X1fr X1no X1kc X1kd X1ka X1h7.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1m6 X1le X1kx X1kb X1ep X1eq X1gf X1em X1gk X1gl X1ek X1ge X1lv X1kz.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib Require Import TopLevel.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pw X0qx.
Import ListNotations.
Open Scope Z_scope.

Local Notation rsegs := Ubsan.M.loaded_segments.

Lemma stdio_exit_ps : stdio_exit_spec_stmt ps_so set_so_ps.
Proof.
apply X1ge.stdio_exit_proof.
- intros s so. reflexivity.
- intros s so so'. reflexivity.
- intros [m brk fa so hdr]. reflexivity.
Qed.

Section Asm.
Context {RCEIL : RunCeiling}.

Hypothesis HARNESS : harness_stmt.

Definition ref_target_run : rtarget_run_stmt :=
X1lv.rtarget_run_proof
X1le.rmalloc_spec
X1kx.rfree_spec_proof
(X1gl.emit_printf_proof PState ps_so set_so_ps)
X1eq.fwritex_stdout_proof
HARNESS
X1m6.RHEAP_frame_proof
X1m6.RHEAP_blocks_nodup_proof
X1m6.RHEAP_blocks_disjoint_proof
X1m6.RHEAP_block_range_proof.

#[using="HARNESS"] Theorem ref_main : rmain_stmt.
Proof.
exact (X1kz.ref_main_proof
X1m6.RHEAP_frame_proof
X1m6.RHEAP_blocks_nodup_proof
X1m6.RHEAP_blocks_disjoint_proof
X1m6.RHEAP_block_range_proof
X1le.rmalloc_spec
X1kx.rfree_spec_proof
X1kb.rfree_keeps_ptr_proof
(X1ek.fprintf_diag_proof PState)
X1ep.fwritex_stderr_proof
X1gf.stdio_write_flush_proof
(@X1em.fwrite_diag_proof PState)
X1gk.towrite_proof
ref_target_run
X1m6.RHEAP_init_proof).
Qed.

#[using="HARNESS"] Theorem ref_impl_from_harness : forall (en : ExecEntry) (inp : ProcInput),
valid_entry (mkImage rsegs Ubsan.M.init_pc Ubsan.M.phdrs) en inp ->
valid_input_core inp ->
alloc_ceiling = bv_unsigned (en_sp en) - 0x800000 ->
run_secret = rnd_w1 (en_draw en) ->
run_canary = canary_of (rnd_w0 (en_draw en)) ->
impl rsegs (at_node rsegs) (prog_ubsan rsegs RSTAGE_ubsan alloc_ceiling (in_argv inp)) (epost (fun (_ : unit) (_ : machine_state) => True))
(ms0F rsegs Ubsan.M.init_pc Ubsan.M.phdrs en inp).
Proof. exact (X1m8.ref_impl_from_main stdio_exit_ps ref_main). Qed.
End Asm.
