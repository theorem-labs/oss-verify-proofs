(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2 X1br.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp X0pw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ea X1fl X1m2 X1m3 X1m5 X1fr X1h7 X1go X1hk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1n8 X1ho X1hm X1hu X1ht X1ih. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nr. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1mc X1mv X1mb X1ma X1mw X1mo X1mt X1mm X1mn X1mr X1ms X1mf X1mg X1mh X1mi X1mj X1mk X1ml X1mp X1mq X1mu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1nt X1rh X1re X1r6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Main.
Context {RCEIL : RunCeiling}.
Variable k : nat.
Variable X : sbinv.
Hypothesis IH : sb_ihyps k X.
Local Notation S := (x_S X). Local Notation OUT := (x_out X). Local Notation A := (x_A X). Local Notation D := (x_D X).
Local Notation STEREO := (x_stereo X). Local Notation lo := (x_lo X). Local Notation a := (x_a X). Local Notation LBL := (x_LBL X).
Local Notation s0 := (x_s X). Local Notation b0 := (x_b0 X). Local Notation canary := (x_canary X). Local Notation st := (x_st X).
Local Notation sp := (x_sp X). Local Notation gp := (x_gp X). Local Notation tp := (x_tp X). Local Notation ra0 := (x_ra X).
Local Notation cs0 := (x_s0 X). Local Notation cs1 := (x_s1 X). Local Notation cs2 := (x_s2 X). Local Notation cs3 := (x_s3 X).
Local Notation cs4 := (x_s4 X). Local Notation cs5 := (x_s5 X). Local Notation cs6 := (x_s6 X). Local Notation cs7 := (x_s7 X).
Local Notation cs8 := (x_s8 X). Local Notation cs9 := (x_s9 X). Local Notation cs10 := (x_s10 X). Local Notation cs11 := (x_s11 X).
Local Notation F0 := (x_F X). Local Notation m0 := (x_m0 X).
Local Notation usp := (bv_unsigned (x_sp X)).
Local Notation FS := (sbd_subframeSize (x_s X)).
Local Notation mo := (sbd_mode (x_s X)).
Local Notation unpackM := (@bits_unpack_unsigned_M PState bptr).
Local Notation peekM := (@bits_peek_M PState bptr).
Local Notation advanceM := (@bits_advance_M PState bptr).
Local Notation remainingM := (@bits_remaining_M PState bptr).
Local Notation LD := (speex_decode io_notify unpackM peekM advanceM remainingM).

#[using="Type"] Lemma at_M_facts : forall low dtx s1 b ms, at_M X low dtx s1 b ms ->
sbd_mode s1 = mo /\ 0 <= sbd_submodeID s1 <= 7 /\ sbd_nbSubframes s1 = 4.
Proof.
intros low dtx s1 b ms AT.
first [ sf_destruct 14%nat AT as Fx fc m kk xra xa0 j ows stb fr _ _ CTX _ | sf_fb; destruct AT as (Fx & fc & m & kk & xra & xa0 & j & ows & stb & fr & _ & _ & CTX & _) ].
first [ sf_destruct 9%nat CTX as _ _ _ _ _ _ INV Emo _ | sf_fb; destruct CTX as (_ & _ & _ & _ & _ & _ & INV & Emo & _) ].
pose proof INV as sfP_; first [ sf_destruct 12%nat sfP_ as _ _ _ _ Inb _ _ _ _ _ Iid _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & Inb & _ & _ & _ & _ & _ & Iid & _) ]. repeat split; try assumption; lia.
Qed.

#[using="RCEIL k IH"] Lemma sb_loop_40 : FS = 40 -> forall n low dtx s1 r sub b ms, Z.of_nat n = 4 - sub -> 0 <= sub <= 3 ->
at_L X low dtx s1 r sub b ms -> evt rsegs (at_T X low dtx s1 (sbsubs_bits n (smr_sm r) b)) ms.
Proof.
intros EFS. induction n as [|n IHn]; intros low dtx s1 r sub b ms Hn Hsub AT; [lia|].
cbn [sbsubs_bits].
eapply evt_cut; [exact (sbL1_40 k X IH EFS _ _ _ _ _ _ _ AT)|]. intros ms1 H1.
eapply evt_cut; [exact (sbL2_40 k X IH EFS _ _ _ _ _ _ _ H1)|]. intros ms2 H2.
eapply evt_cut; [exact (sbL3_40 k X IH EFS _ _ _ _ _ _ _ H2)|]. intros ms3 H3.
destruct H3 as [[LT H3] | [E3 H3]].
- eapply (IHn _ _ _ _ (sub + 1)); [lia | lia | exact H3].
- destruct n; [| lia]. cbn [sbsubs_bits]. apply evt_done. exact H3.
Qed.
#[using="RCEIL k IH"] Lemma sb_loop_80 : FS = 80 -> forall n low dtx s1 r sub b ms, Z.of_nat n = 4 - sub -> 0 <= sub <= 3 ->
at_L X low dtx s1 r sub b ms -> evt rsegs (at_T X low dtx s1 (sbsubs_bits n (smr_sm r) b)) ms.
Proof.
intros EFS. induction n as [|n IHn]; intros low dtx s1 r sub b ms Hn Hsub AT; [lia|].
cbn [sbsubs_bits].
eapply evt_cut; [exact (sbL1_80 k X IH EFS _ _ _ _ _ _ _ AT)|]. intros ms1 H1.
eapply evt_cut; [exact (sbL2_80 k X IH EFS _ _ _ _ _ _ _ H1)|]. intros ms2 H2.
eapply evt_cut; [exact (sbL3_80 k X IH EFS _ _ _ _ _ _ _ H2)|]. intros ms3 H3.
destruct H3 as [[LT H3] | [E3 H3]].
- eapply (IHn _ _ _ _ (sub + 1)); [lia | lia | exact H3].
- destruct n; [| lia]. cbn [sbsubs_bits]. apply evt_done. exact H3.
Qed.
#[using="RCEIL k IH"] Lemma sb_loop : forall low dtx s1 r b ms,
at_L X low dtx s1 r 0 b ms -> evt rsegs (at_T X low dtx s1 (sbsubs_bits 4 (smr_sm r) b)) ms.
Proof.
intros low dtx s1 r b ms AT. destruct (FS_cases k X IH) as [E|E].
- eapply (sb_loop_40 E 4%nat _ _ _ _ 0); [reflexivity | lia | exact AT].
- eapply (sb_loop_80 E 4%nat _ _ _ _ 0); [reflexivity | lia | exact AT].
Qed.
#[using="RCEIL k IH"] Lemma sb_tail : forall low dtx s1 b ms, at_T X low dtx s1 b ms -> evt rsegs (at_X X 0 (set_sbd_first s1 0) low b) ms.
Proof.
intros low dtx s1 b ms AT. destruct (FS_cases k X IH) as [E|E].
- exact (sbT_40 k X IH E _ _ _ _ _ AT).
- exact (sbT_80 k X IH E _ _ _ _ _ AT).
Qed.

Definition END_POST (r : Z * (sbd_state bptr * dec_state bptr) * bits_st bptr) (st' : PState) (ms' : machine_state) : Prop :=
st' = st /\ let '(ret, sl, b') := r in let '(s', low') := sl in at_END X ret s' low' b' ms'.

#[using="RCEIL k IH"] Lemma end_of_X : forall ret s low b ms, at_X X ret s low b ms -> evt rsegs (END_POST (ret, (s, low), b) st) ms.
Proof.
intros ret s low b ms AT. eapply evt_cut; [exact (sbX k X IH _ _ _ _ _ AT)|].
intros ms1 H1. apply evt_done. split; [reflexivity| exact H1].
Qed.

#[using="RCEIL k IH"] Theorem sb_decode_main : forall (OUTL : Z) (low0 : dec_state bptr) (j : sb_junk) (ows : list word) (stb : list byte)
(t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32),
sbctx0 X OUTL m0 s0 low0 b0 j ows stb -> stk rsegs m0 lo usp -> frm0 fc ->
implM rsegs (sb_decode io_notify unpackM peekM remainingM s0 low0 LD b0 0) st END_POST
(MS (mkR ra0 sp gp tp t0 t1 t2 cs0 cs1 (Z_to_bv 64 S) (Z_to_bv 64 A) (Z_to_bv 64 OUT) a3 a4 a5 a6 a7 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 t3 t4 t5 t6)
F0 (Z_to_bv 64 A_sb_decode) fc None m0 (seg_rom rsegs)).
Proof.
intros OUTL low0 j ows stb t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc CTX STK FRM.
pose proof (ih_inv0 _ _ IH) as INV0. pose proof INV0 as sfP_; first [ sf_destruct 11%nat sfP_ as Imo _ _ _ _ _ _ _ _ Ies _ | sf_fb; destruct sfP_ as (Imo & _ & _ & _ & _ & _ & _ & _ & _ & Ies & _) ].
eapply implM_eqM. { rewrite (sb_decode_unfold io_notify s0 low0 _ b0 0 Ies). reflexivity. }
rewrite Z.add_0_l.
destruct (speex_decoder_ctl low0 (CtlSetInnovationSave (sbd_frame_size s0))) as [u1 low1] eqn:EC1.
apply implM_from_evt. eapply evt_cut.
{ eapply (sbP1 k X IH OUTL low0 j ows stb); [exact CTX | exact STK | exact FRM]. }
intros ms1 HDEC. apply evt_done. rewrite EC1 in HDEC. cbn [snd] in HDEC.
eapply implM_bind. { exact (sbP_dec k X IH _ _ HDEC). }
intros [[ret low2] b1] st1 ms2 [-> HRET].
destruct (speex_decoder_ctl low2 CtlGetDtxStatus) as [dtx low3] eqn:EC2.
pose proof (sbP2 k X IH _ _ _ _ HRET) as E2. unfold QP2 in E2. rewrite EC2 in E2.
destruct (ret =? 0) eqn:ER; cbn [negb].
2:{
apply implM_ret. eapply evt_cut; [exact E2|]. intros ms3 HX. exact (end_of_X _ _ _ _ _ HX). }
apply implM_from_evt. eapply evt_cut; [exact E2|]. intros ms3 HW. apply evt_done.
eapply implM_bind. { exact (sbW k X IH _ _ _ _ HW). }
intros sr st2 ms4 [-> HQW].
destruct sr as [[s1 b2] | [s1 b2]]; cbn [QW] in HQW.
2:{
apply implM_ret. exact (end_of_X _ _ _ _ _ HQW). }
pose proof (at_M_facts _ _ _ _ _ HQW) as (Emo1 & Hid & Inb1).
pose proof (sbM k X IH _ _ _ _ _ HQW) as EM. unfold QM in EM.
rewrite Emo1.
destruct (sb_smrec_cases mo (sbd_submodeID s1) Imo Hid) as [(SP0 & SAT & SMN) | (r & SAT & INr & SPE & SPnz & SMS & _)]; rewrite SAT in EM.
-
rewrite SMN. apply implM_ret.
eapply evt_cut; [exact EM|]. intros ms5 HN.
eapply evt_cut; [exact (sbN k X IH _ _ _ _ _ HN)|]. intros ms6 HX. exact (end_of_X _ _ _ _ _ HX).
-
rewrite SMS.
destruct (speex_decoder_ctl low3 CtlGetPiGain) as [u4 low4] eqn:EC4.
destruct (speex_decoder_ctl low4 CtlGetExc) as [u5 low5] eqn:EC5.
eapply implM_bind_run; [apply lsp_unquant_run|].
eapply implM_bind_run; [apply sb_decode_subframes_run|].
apply implM_ret. rewrite Inb1. change (Z.to_nat 4) with 4%nat.
first [ pose proof (sb_smrec_at_some mo _ r SAT) as sfP_; sf_destruct 6%nat sfP_ as _ _ _ _ LSPH _ | sf_fb; destruct (sb_smrec_at_some mo _ r SAT) as (_ & _ & _ & _ & LSPH & _) ]. rewrite LSPH.
eapply evt_cut; [exact EM|]. intros ms5 HV.
pose proof (sbV1 k X IH _ _ _ _ _ _ HV) as EV1. rewrite EC4 in EV1. cbn [snd] in EV1. rewrite EC5 in EV1. cbn [snd] in EV1.
eapply evt_cut; [exact EV1|]. intros ms6 HV1.
eapply evt_cut; [exact (sbV2 k X IH _ _ _ _ _ _ HV1)|]. intros ms7 HV2.
eapply evt_cut; [exact (sbV3 k X IH _ _ _ _ _ _ HV2)|]. intros ms8 HL.
eapply evt_cut; [exact (sb_loop _ _ _ _ _ _ HL)|]. intros ms9 HT.
eapply evt_cut; [exact (sb_tail _ _ _ _ _ HT)|]. intros ms10 HX. exact (end_of_X _ _ _ _ _ HX).
Qed.
End Main.
