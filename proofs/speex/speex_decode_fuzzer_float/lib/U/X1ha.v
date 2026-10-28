(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bk X1bq X1br X1c0.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qn X0qc X0qp X0qb X0pt.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1fl X1ea X1fr X1no X1h7 X1kd X1k9.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ik X1ij X1ii X1il X1im X1is X1ip X1iq X1in X1ja X1iu X1j8 X1j4 X1j9 X1it X1j2 X1iv X1iw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1g3 X1g1 X1g6 X1g5 X1g2.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1go X1hk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1hl. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1h9 X1gy X1gn X1gp X1gq X1gr X1gs X1gt.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1hg X1hb X1hc X1hd X1he X1hf X1hh X1hi X1hj X1gz X1gx.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1gu X1h6 X1h0 X1h1 X1h2 X1h3 X1h4 X1h5.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1ff X1fd.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1r4 X1r6 X1qz X1r0 X1r1 X1nt X1rg X1rh X1re X1od.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section MAIN.
Context {RCEIL : RunCeiling}.

Variable dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop.
Hypothesis DRF : dec_rep_frame_stmt dec_rep.
Hypothesis DINIT : rspx_decoder_init_stmt dec_rep.
Hypothesis DCTL : rspx_decoder_ctl_stmt dec_rep.
Hypothesis DDESTROY : rspx_decoder_destroy_stmt dec_rep.
Hypothesis DECODE : rspx_decode_stmt dec_rep.
Hypothesis DSTEREO : rspx_decode_stereo_stmt.
Hypothesis P2H : rspx_packet_to_header_stmt.

Hypothesis FWE : fwritex_stderr_stmt.
Hypothesis FLS : stdio_write_flush_stmt.
Hypothesis HRR : bits_realloc_stmt rtop_known.
Hypothesis RCAL : bits_calloc_stmt.
Hypothesis RMALLOC : rmalloc_stmt.
Hypothesis RFREE : rfree_stmt.
Hypothesis OREALLOC : ogg_realloc_stmt rtop_known.
Hypothesis RHF : rheap_frame_stmt.
Hypothesis RBR : rheap_block_range_stmt.
Hypothesis RND : rheap_blocks_nodup_stmt.
Hypothesis RBD : rheap_blocks_disjoint_stmt.
Hypothesis RTK : rheap_top_known_stmt.

Hypothesis OSINIT : ogg_stream_init_stmt2.
Hypothesis OPAGEIN : ogg_stream_pagein_stmt2.

Section CTX.
Variable c : hcx.
Hypothesis CX : hcx_ok c.

Notation POSTQ := (fun (r : Z) st ms => harness_post (x_ra c) (x_sp c) (x_gp c) (wz RATP) (x_s0 c) (x_s1 c) (x_s2 c) (x_s3 c) (x_s4 c) (x_s5 c)
(x_s6 c) (x_s7 c) (x_s8 c) (x_s9 c) (x_s10 c) (x_s11 c) (x_st0 c) (x_LB0 c) (x_AB c) (x_lo c) (x_m0 c) r st ms).
Notation PPOST br0 := (fun (o : outcome bptr) st ms => match o with
| Cont h' => PGX dec_rep c h' st ms /\ h_bytes_remaining h' = br0
| Returned => HFIN c st ms end).

#[using="DRF DINIT DCTL DDESTROY P2H RFREE RHF RBR RND RBD CX"] Lemma hdr_path : pkt_path_stmt dec_rep c (fun h op => PKH dec_rep c h op).
Proof.
intros fuel' h op pn st ms br0 oy0 PH EOY EBR BUD K.
eapply (hdr_p2h dec_rep P2H RFREE RHF RBR RND c CX); [exact PH| exact EOY| exact EBR| exact BUD|].
intros blk hd st1 ms1 HM1.
eapply (hdr_checks dec_rep DINIT RFREE RBR RND c CX); [exact HM1|]. intros d st2 ms2 HS2 DM ID MBV.
eapply (hdr_ctls1 dec_rep DRF DCTL DDESTROY RFREE RHF RBR RND RBD c CX); [exact HS2|]. intros d2 fs rate st3 ms3 HR3.
eapply (hdr_ctls2 dec_rep DCTL DDESTROY RFREE RHF RBR RND RBD c CX); [exact HR3|]. intros d3 st4 ms4 HC4.
eapply (hdr_chan dec_rep DRF DCTL RHF RBR RND RBD c CX); [exact HC4|]. intros dJ ch2 st5 ms5 HJ5.
eapply (hdr_fin dec_rep DRF DCTL DDESTROY RFREE RHF RBR RND RBD c CX); [exact HJ5| exact EOY| exact EBR| exact K].
Qed.

#[using="DRF DINIT DCTL DDESTROY DECODE DSTEREO P2H FWE FLS HRR RFREE RHF RBR RND RBD RTK CX"] Lemma packet_loop_ok : forall (n fuel : nat) h pn st ms,
PK dec_rep c h st ms ->
(Z.to_nat (os_lacing_fill (h_os h) - os_lacing_returned (h_os h)) < n)%nat ->
(Z.to_nat (os_lacing_fill (h_os h) - os_lacing_returned (h_os h)) < fuel)%nat ->
implM rsegs (packet_loopP fuel h pn) st (PKPOST dec_rep c (h_bytes_remaining h) (h_oy h)) ms.
Proof.
exact (pkt_loop_ok dec_rep DRF RHF RBR c CX hdr_path
(data_path dec_rep DRF DECODE DSTEREO FWE FLS HRR RHF RBR RND RBD RTK c CX)).
Qed.

#[using="Type"] Lemma PGB_hpend : forall h og st ms, PGB dec_rep c h og st ms -> 0 <= hpend h.
Proof.
intros h og st ms PG.
first [ sf_destruct 32%nat PG as x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m x nbr brem0 s0w s3w s8w OP _ _ _ _ _ _ (cold & PB) | sf_fb; destruct PG as (x1 & t0 & t1 & t2 & a0 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & x & nbr & brem0 & s0w & s3w & s8w & OP & _ & _ & _ & _ & _ & _ & (cold & PB)) ]. lia.
Qed.

#[using="DRF DINIT DCTL DDESTROY DECODE DSTEREO P2H FWE FLS HRR RFREE RHF RBR RND RBD RTK OSINIT OPAGEIN CX"] Lemma page_body_ok : forall (n : nat) fuel' (h h1 : hstate bptr) og st1 ms1,
(forall h' st' ms', (PG1 dec_rep c h' st' ms' \/ PGN dec_rep c h' st' ms') ->
(Z.to_nat (hpend h') < n)%nat -> (Z.to_nat (hpend h') < fuel')%nat -> h_bytes_remaining h' = h_bytes_remaining h ->
implM rsegs (page_loopP fuel' h') st' (PPOST (h_bytes_remaining h)) ms') ->
PGB dec_rep c h1 og st1 ms1 -> h_bytes_remaining h1 = h_bytes_remaining h ->
(Z.to_nat (hpend h1) < n)%nat -> (Z.to_nat (hpend h1) < fuel')%nat ->
implM rsegs (page_bodyP fuel' h1 og) st1 (PPOST (h_bytes_remaining h)) ms1.
Proof.
intros n fuel' h h1 og st1 ms1 IH PGB1 EBR1 MN MF.
eapply (page_sinit dec_rep DRF RBR RND OSINIT c CX); [exact PGB1|]. intros h2 st2 ms2 PGS2 EOY2 EBR2.
rewrite <- EOY2.
eapply (page_serial dec_rep DRF RHF RBR c CX); [exact PGS2|]. intros h3 st3 ms3 PGP3 EOY3 EBR3 EH3.
eapply (page_pagein dec_rep DRF RHF RBR RND RTK OPAGEIN c CX _ fuel' h2 h3 og); [exact PGP3| exact EOY3|].
intros h4 st4 ms4 PGG4 EOY4 EBR4.
replace (h_oy h2) with (h_oy h4) by (rewrite EOY4, EOY3; reflexivity).
eapply (page_granule dec_rep DRF RHF RBR c CX); [exact PGG4| | |].
-
intros h' st' ms' CL. eapply (clean_ok dec_rep DRF DDESTROY RFREE RHF RBR RND c CX); [exact CL|].
intros st'' ms'' HF. apply implM_ret. apply evt_done. exact HF.
-
intros h5 st5 ms5 PK5 EOY5 EBR5. eapply implM_bind.
{ apply (packet_loop_ok (S (Z.to_nat (os_lacing_fill (h_os h5) - os_lacing_returned (h_os h5))))); [exact PK5| lia| unfold packet_fuel; lia]. }
cbv beta. intros [h6|] st6 ms6 PP.
+ destruct PP as (PGN6 & EBR6 & EOY6). apply IH; [right; exact PGN6| | |];
unfold hpend in *; rewrite ?EOY6, ?EOY5, ?EOY4, ?EOY3, ?EOY2; first [lia| congruence].
+ apply implM_ret. apply evt_done. exact PP.
-
intros h5 st5 ms5 PGN5 EOY5 EBR5. apply IH; [right; exact PGN5| | |];
unfold hpend in *; rewrite ?EOY5, ?EOY4, ?EOY3, ?EOY2; first [lia| congruence].
Qed.

#[using="DRF DINIT DCTL DDESTROY DECODE DSTEREO P2H FWE FLS HRR RFREE RHF RBR RND RBD RTK OSINIT OPAGEIN CX"] Lemma page_loop_ok : forall (n fuel : nat) (h : hstate bptr) st ms,
(PG1 dec_rep c h st ms \/ PGN dec_rep c h st ms) ->
(Z.to_nat (hpend h) < n)%nat -> (Z.to_nat (hpend h) < fuel)%nat ->
implM rsegs (page_loopP fuel h) st (PPOST (h_bytes_remaining h)) ms.
Proof.
induction n as [|n IH]; intros fuel h st ms PG MN MF; [lia|].
destruct fuel as [|fuel']; [lia|].
assert (BODY : forall h1 og st1 ms1, PGB dec_rep c h1 og st1 ms1 -> h_bytes_remaining h1 = h_bytes_remaining h -> hpend h1 + 27 <= hpend h ->
implM rsegs (page_bodyP fuel' h1 og) st1 (PPOST (h_bytes_remaining h)) ms1).
{ intros h1 og st1 ms1 PGB1 EBR1 PEND.
pose proof (PGB_hpend _ _ _ _ PGB1) as NN.
apply (page_body_ok n fuel' h h1 og st1 ms1); [| exact PGB1| exact EBR1| lia| lia].
intros h' st' ms' PG' MN' MF' EBR'. rewrite <- EBR'. apply IH; [exact PG'| lia| lia]. }
destruct PG as [PG|PG].
- eapply (page_head1 dec_rep DRF RHF RBR RND RBD c CX); [exact PG| exact BODY].
- eapply (page_headN dec_rep DRF RHF RBR RND RBD c CX); [exact PG| exact BODY].
Qed.

#[using="DRF DINIT DCTL DDESTROY DECODE DSTEREO P2H FWE FLS HRR RFREE RHF RBR RND RBD RTK OSINIT OPAGEIN CX"] Lemma page_for_chunk : forall h st ms, PG1 dec_rep c h st ms ->
implM rsegs (page_loopP (page_fuel (h_oy h)) h) st (PGPOST dec_rep c h) ms.
Proof.
intros h st ms PG. change (PGPOST dec_rep c h) with (PPOST (h_bytes_remaining h)).
apply (page_loop_ok (S (Z.to_nat (hpend h)))); [left; exact PG| lia| unfold page_fuel, hpend; lia].
Qed.

#[using="DRF DINIT DCTL DDESTROY DECODE DSTEREO P2H FWE FLS HRR RMALLOC RFREE OREALLOC RHF RBR RND RBD RTK OSINIT OPAGEIN CX"] Lemma chunks_ok : forall h st ms,
CUTC dec_rep c h st ms -> h = h0 c (h_bits h) ->
implM rsegs (X1qx.mbind (chunk_loop raw_malloc raw_calloc raw_realloc raw_free io_notify io_warning
bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M
(chunk_fuel (zlength (x_payload c))) (x_payload c) (h0 c (h_bits h)))
(fun o => match o with
| Returned => X1qx.mret 0
| Cont h' => X1qx.mbind (cleanup raw_free (St:=PState) h') (fun _ => X1qx.mret 0) end))
st POSTQ ms.
Proof.
intros h st ms CC E. rewrite <- E.
apply (chunk_loop_ok dec_rep DRF RMALLOC RFREE OREALLOC RHF RBR RND RBD RTK c CX page_for_chunk).
- intros B k Q h' st' ms' CL KF. eapply (clean_ok dec_rep DRF DDESTROY RFREE RHF RBR RND c CX); [exact CL| exact KF].
- exact CC.
- rewrite E. unfold chunk_fuel. cbn [h_bytes_remaining h0]. lia.
Qed.
End CTX.

#[using="dec_rep DRF DINIT DCTL DDESTROY DECODE DSTEREO P2H FWE FLS HRR RCAL RMALLOC RFREE OREALLOC RHF RBR RND RBD RTK OSINIT OPAGEIN"] Theorem harness_proof : harness_stmt.
Proof.
unfold harness_stmt. intros until errv.
intros HP PAY PF P0 P16 PL PIN TP SEW AUX SPAB ABB ST CEIL LO ERR MI FRM -> SP16 -> ->.
set (c := HCX sp ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s m LB pb P payload B lo).
assert (CX : hcx_ok c).
{ unfold hcx_ok, c. cbn. pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R.
repeat (split; [first [assumption| lia]|]). lia. }
eapply (h0_entry dec_rep RCAL RFREE RHF RBR c CX); cbn [x_st0 x_LB0 x_m0 x_P x_payload x_AB x_lo x_sp c];
[| exact HP| exact PAY| exact TP| exact SEW| exact AUX| exact ST| | exact MI| exact FRM].
2:{ unfold RATP in ERR. rewrite unsigned_lit in ERR by lia. exact ERR. }
intros h st' ms CC E. cbv beta. apply (chunks_ok c CX h st' ms CC E).
Qed.
End MAIN.

