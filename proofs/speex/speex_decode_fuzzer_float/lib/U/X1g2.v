(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bk.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qn X0px X0qc X0qp.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qv X1qx X1r3 X1r4 X1nt X1rd X1oc X1ri.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ei X1fl X1ea X1jh. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1jg. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1fr X1je X1ji X1gk X1ek.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1g5.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition BITS_STR_TOP : Z := 0x20000.

Lemma BITS_STR_TOP_ok : 0x106b0 <= BITS_STR_TOP.
Proof. unfold BITS_STR_TOP. lia. Qed.

Lemma stderr_wfile_kept : forall m m', range_kept m m' BITS_RSTDERR (BITS_RSTDERR + 232) -> stderr_wfile m -> stderr_wfile m'.
Proof.
intros m m' RK sfH_; first [ sf_destruct 7%nat sfH_ as flags mode e wend tail FC FL | sf_fb; destruct sfH_ as (flags & mode & e & wend & tail & FC & FL) ]. first [ unshelve sf_eexists 5%nat; [ exact (flags) | exact (mode) | exact (e) | exact (wend) | exact (tail) | ] | sf_fb; exists flags, mode, e, wend, tail ]. split; [|exact FL].
eapply (pres_except_rw_cells rsegs (fun a => BITS_RSTDERR <= a < BITS_RSTDERR + 232) []); [| exact FC|].
- intros a Ha Hc _. exact (RK a Ha Hc).
- intros a Ha. split; [|intros X; exact X]. cbn in Ha. unfold BITS_RSTDERR. lia.
Qed.

Lemma rheap_ssp {RCEIL : RunCeiling} : forall s LB m, RHEAP s LB m -> ssp_cells m run_canary.
Proof.
intros s LB m sfH_; first [ sf_destruct 6%nat sfH_ as st LB0 _ _ MR _ | sf_fb; destruct sfH_ as (st & LB0 & _ & _ & MR & _) ]. first [ sf_destruct 4%nat MR as _ _ G _ | sf_fb; destruct MR as (_ & _ & G & _) ]. first [ sf_destruct 5%nat G as _ _ _ G4 G5 | sf_fb; destruct G as (_ & _ & _ & G4 & G5) ].
unfold ssp_cells, got_ssp, ssp_guard. split; [exact G4| exact G5].
Qed.

Section G.
Context {RCEIL : RunCeiling}.
Hypothesis FWE : fwritex_stderr_stmt.
Hypothesis FLS : stdio_write_flush_stmt.

#[using="FWE FLS"] Lemma bits_notify_of_stdio : bits_notify_stmt s_notify stderr_wfile ssp_cells BITS_STR_TOP.
Proof.
unfold bits_notify_stmt, bits_fprintf_stmt. intros until canary.
intros Ha0 Ha1 sfH_; first [ sf_destruct 8%nat sfH_ as slack BY HF SLK LEN POS DJ GA | sf_fb; destruct sfH_ as (slack & BY & HF & SLK & LEN & POS & DJ & GA) ]; intros SF ST LO GLO QHI SSP MI FRM.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
unfold BITS_FPRINTF_DEPTH, BITS_GLOBALS_TOP, BITS_STR_TOP, BITS_INT_MAX, BITS_RSTDERR, BITS_FMT_notify, A_fprintf in *.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. unfold bits_zb in AB. rewrite length_app, length_map in AB. cbn [length] in AB.
unfold zlength in *.
unfold s_notify.
eapply (X1qx.implM_mono rsegs).
- eapply (fprintf_stderr_proof FWE FLS) with (fmt := FMT_notify) (args := [PA_s s]) (A := A_FMT_notify) (lo := lo) (canary := canary);
unfold FPRINTF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, VF_FRAME, zlength;
[ exact Ha0 | exact Ha1 | exact SF
| apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_notify; lia | unfold A_FMT_notify, FMT_notify, zlength; cbn - [Z.add Z.le]; lia]
| apply forall_range_b; vm_compute; reflexivity
| vm_compute; reflexivity
| cbn [args_ok arg_ok]; split; [|exact I]; exists slack; unfold zlength; repeat (split; [first [exact BY | exact HF | exact SLK | lia] |]); lia
| apply printf_pieces_notify; unfold zlength, INT_MAX in *; lia
| vm_compute; reflexivity
| exact ST | lia | lia | lia | exact SSP | exact MI | exact FRM
| unfold A_FMT_notify; lia
| unfold A_FMT_notify, FMT_notify, zlength; cbn -[Z.add Z.le]; lia ].
- intros [] st' ms' H. exact H.
Qed.

#[using="FWE FLS"] Lemma bits_warning_of_stdio : bits_warning_stmt s_warning stderr_wfile ssp_cells BITS_STR_TOP.
Proof.
unfold bits_warning_stmt, bits_fprintf_stmt. intros until canary.
intros Ha0 Ha1 sfH_; first [ sf_destruct 8%nat sfH_ as slack BY HF SLK LEN POS DJ GA | sf_fb; destruct sfH_ as (slack & BY & HF & SLK & LEN & POS & DJ & GA) ]; intros SF ST LO GLO QHI SSP MI FRM.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
unfold BITS_FPRINTF_DEPTH, BITS_GLOBALS_TOP, BITS_STR_TOP, BITS_INT_MAX, BITS_RSTDERR, BITS_FMT_warning, A_fprintf in *.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. unfold bits_zb in AB. rewrite length_app, length_map in AB. cbn [length] in AB.
unfold zlength in *.
unfold s_warning.
eapply (X1qx.implM_mono rsegs).
- eapply (fprintf_stderr_proof FWE FLS) with (fmt := FMT_warning) (args := [PA_s s]) (A := A_FMT_warning) (lo := lo) (canary := canary);
unfold FPRINTF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, VF_FRAME, zlength;
[ exact Ha0 | exact Ha1 | exact SF
| apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_warning; lia | unfold A_FMT_warning, FMT_warning, zlength; cbn - [Z.add Z.le]; lia]
| apply forall_range_b; vm_compute; reflexivity
| vm_compute; reflexivity
| cbn [args_ok arg_ok]; split; [|exact I]; exists slack; unfold zlength; repeat (split; [first [exact BY | exact HF | exact SLK | lia] |]); lia
| apply printf_pieces_warning; unfold zlength, INT_MAX in *; lia
| vm_compute; reflexivity
| exact ST | lia | lia | lia | exact SSP | exact MI | exact FRM
| unfold A_FMT_warning; lia
| unfold A_FMT_warning, FMT_warning, zlength; cbn -[Z.add Z.le]; lia ].
- intros [] st' ms' H. exact H.
Qed.

Definition speex_bits_read_from_std (rtop_known : PState -> bptr -> Prop)
(HR : bits_realloc_stmt rtop_known) (HFR : rheap_frame_stmt) (HBR : rheap_block_range_stmt)
(HBD : rheap_blocks_disjoint_stmt) (HBN : rheap_blocks_nodup_stmt) :=
speex_bits_read_from_spec s_notify s_warning stderr_wfile ssp_cells BITS_STR_TOP rtop_known
bits_notify_of_stdio bits_warning_of_stdio HR HFR HBR HBD BITS_STR_TOP_ok HBN stderr_wfile_kept rheap_ssp.
End G.
