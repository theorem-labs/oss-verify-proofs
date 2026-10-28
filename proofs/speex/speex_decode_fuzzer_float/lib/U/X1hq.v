(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3 X1oc X1ri.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ea X1fl X1jh X1fr X1ek.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm X1hs X1hr X1g9 X1g8 X1fa X1fb X1f9 X1ej X1fk X1fm X1gd X1ef X1f1 X1f3 X1fg.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition NB_STR_TOP : Z := 0x20000.
Lemma NB_STR_TOP_ok : 0x104d0 <= NB_STR_TOP.
Proof. unfold NB_STR_TOP. lia. Qed.

Lemma stderr_wfile_serr_frame : serr_frame stderr_wfile.
Proof.
unfold serr_frame. intros m m' W sfH_; first [ sf_destruct 7%nat sfH_ as flags mode e wend tail FC FL | sf_fb; destruct sfH_ as (flags & mode & e & wend & tail & FC & FL) ]; intros MU WM DJ.
first [ unshelve sf_eexists 5%nat; [ exact (flags) | exact (mode) | exact (e) | exact (wend) | exact (tail) | ] | sf_fb; exists flags, mode, e, wend, tail ]. split; [|exact FL].
eapply rw_cells_transport; [exact FC | exact MU | exact WM |].
exact DJ.
Qed.

Lemma ssp_cells_sspc_frame : sspc_frame ssp_cells.
Proof.
unfold sspc_frame, ssp_cells, got_ssp, ssp_guard. intros m m' W c [G1 G2] MU WM D1 D2. split.
- eapply rw_cells_transport; [exact G1 | exact MU | exact WM | exact D1].
- eapply rw_cells_transport; [exact G2 | exact MU | exact WM | exact D2].
Qed.

Section Link.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.

Hypothesis FWE : fwritex_stderr_stmt.
Hypothesis FLS : stdio_write_flush_stmt.

Let H_multicomb : multicomb_stmt := multicomb_proof.
Let H_3tap : forall p, ltp_params_ok p -> ltp_unquant_stmt (ptr:=ptr) (LtpPitchUnquant3tap p)
:= pitch_unquant_3tap_proof.
Let H_split : forall p, scb_params_ok p -> innov_unquant_stmt (ptr:=ptr) (InnovSplitCbShapeSignUnquant p)
:= split_cb_shape_sign_unquant_proof.
Let H_exp : exp_stmt := exp_proof.
Let H_lspi : lsp_interpolate_stmt := lsp_interpolate_proof.
Let H_l2l : lsp_to_lpc_stmt := lsp_to_lpc_proof.
Let H_lsp : forall k, lsp_unquant_stmt (ptr:=ptr) k :=
fun k => match k with
| LspUnquantLbr => lsp_unquant_lbr_proof
| LspUnquantNb => lsp_unquant_nb_proof
| LspUnquantHigh => lsp_unquant_high_proof
end.
Let H_ltp : forall k, match k with LtpPitchUnquant3tap p => ltp_params_ok p | _ => True end -> ltp_unquant_stmt (ptr:=ptr) k :=
fun k => match k with
| LtpForcedPitchUnquant => fun _ => forced_pitch_unquant_proof
| LtpPitchUnquant3tap p => H_3tap p
end.
Let H_innov : forall k, match k with InnovSplitCbShapeSignUnquant p => scb_params_ok p | _ => True end -> innov_unquant_stmt (ptr:=ptr) k :=
fun k => match k with
| InnovNoiseCodebookUnquant => fun _ => noise_codebook_unquant_proof
| InnovSplitCbShapeSignUnquant p => H_split p
end.

#[using="FWE FLS"] Lemma nb_notify_of_stdio : nb_notify_stmt s_notify stderr_wfile ssp_cells NB_STR_TOP.
Proof.
unfold nb_notify_stmt. intros until canary.
intros Ha0 Ha1 sfH_; first [ sf_destruct 8%nat sfH_ as slack BY HF SLK LEN POS DJ GA | sf_fb; destruct sfH_ as (slack & BY & HF & SLK & LEN & POS & DJ & GA) ]; intros SF ST LO GLO QHI SSP MI FRM.
unfold NB_FPRINTF_DEPTH, NB_GLOBALS_TOP, NB_STR_TOP, NB_RSTDERR, NB_FMT_notify, A_fprintf in *.
eapply (X1qx.implM_mono rsegs).
- eapply (fprintf_notify_proof FWE FLS) with (lo := lo) (canary := canary);
unfold FPRINTF_DEPTH, GLOBALS_TOP, STATIC_SPLIT;
[ exact Ha0 | exact Ha1 | | exact SF | exact ST | lia | lia | exact QHI | exact SSP | exact MI | exact FRM ].
exists slack. unfold X1oc.INT_MAX. repeat (split; [assumption|]). exact GA.
- intros [] st' ms' sfH_; first [ sf_destruct 28%nat sfH_ as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft fc' m' -> MU WM MI' FRM' FOK ST' SF' SSP' -> | sf_fb; destruct sfH_ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FOK & ST' & SF' & SSP' & ->) ].
first [ unshelve sf_eexists 18%nat; [ exact (t0') | exact (t1') | exact (t2') | exact (a0') | exact (a1') | exact (a2') | exact (a3') | exact (a4') | exact (a5') | exact (a6') | exact (a7') | exact (t3') | exact (t4') | exact (t5') | exact (t6') | exact (Ft) | exact (fc') | exact (m') | ] | sf_fb; exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', Ft, fc', m' ].
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact FRM'|].
split; [exact (Fok10_agree _ _ FOK)|].
split; [exact ST'|]. split; [exact SF'|]. split; [exact SSP'|]. reflexivity.
Qed.

Local Notation NBREP := (nbstate_rep rsegs NB_MODE_PTR NB_SUBMODES_PTR A_speex_default_user_handler A_speex_std_stereo_request_handler).

#[using="FWE FLS H_multicomb H_3tap H_split H_exp H_lspi H_l2l H_lsp H_ltp H_innov"] Lemma nb_hyps_intro : forall (X : nbinv ptr),
x_serr X = stderr_wfile -> x_sspc X = ssp_cells ->
nb_layout (x_st X) (x_out X) (x_A X) (x_D X) (sb_buf_size (x_b0 X)) (x_stereo X) (x_isv X) (x_lo X) (bv_unsigned (x_sp X)) ->
x_lo X + NB_DECODE_DEPTH <= bv_unsigned (x_sp X) -> bv_unsigned (x_sp X) < 2^63 ->
nb_inv (x_st0 X) ->
match nb_innov_save (x_st0 X) with None => True | Some k => x_isv X = x_out X + 4 * k end ->
x_st X mod 8 = 0 -> x_st X + NBSTATE_SIZEOF < 2^63 ->
x_out X mod 4 = 0 -> x_stereo X mod 4 = 0 -> bv_unsigned (x_sp X) mod 16 = 0 ->
nb_tables (x_m0 X) -> stderr_wfile (x_m0 X) -> ssp_cells (x_m0 X) (x_canary X) ->
nb_hyps s_notify NB_STR_TOP X.
Proof.
intros X E1 E2 LAY LO SPX INV ISV AL HI OUT4 STER4 SP16 TAB SE SS.
constructor; rewrite ?E1, ?E2; try assumption.
- exact stderr_wfile_serr_frame.
- exact ssp_cells_sspc_frame.
- exact nb_notify_of_stdio.
- exact NB_STR_TOP_ok.
- exact (inband_handler_proof H_exp).
- exact user_handler_proof.
- exact memmove_proof.
- exact bw_lpc_w_proof.
- exact compute_rms16_w_proof.
- exact signal_mul_w_proof.
- exact sanitize_values32_w_proof.
- exact iir_mem16_w_proof.
- exact highpass_w_proof.
Qed.

#[using="FWE FLS H_multicomb H_3tap H_split H_exp H_lspi H_l2l H_lsp H_ltp H_innov"] Theorem nb_decode_linked : nb_decode_stmt (ptr:=ptr) s_notify stderr_wfile ssp_cells.
Proof.
unfold nb_decode_stmt. intros until m.
intros REP HISV BR BOK XO LO XI LI XS LS TAB SE SS STK DEP SPX LAY HI OUT4 STER4 SP16 -> -> -> MI FRM.
first [ sf_destruct 7%nat REP as AL POS INV j JOK CBS CELLS | sf_fb; destruct REP as (AL & POS & INV & j & JOK & CBS & CELLS) ].
apply (proj1 (nb_pieces_iff rsegs _ _ _ _ _ _ _ _ _ JOK)) in CELLS.
set (X := NBI ptr stderr_wfile ssp_cells ST OUT A D STEREO ISV lo canary st b ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m).
assert (NH : nb_hyps s_notify NB_STR_TOP X) by (apply nb_hyps_intro; cbn; first [reflexivity | assumption]).
exact (nb_decode_main s_notify NB_STR_TOP X NH s j ows iws sws t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc
CELLS JOK CBS BR BOK XO LO XI LI XS LS STK MI FRM).
Qed.
End Link.
