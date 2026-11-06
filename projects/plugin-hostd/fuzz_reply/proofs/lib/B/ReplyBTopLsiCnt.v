(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_LLVMFuzzerTestOneInput_top_x.v; 84 of its 189 lines of code are new or changed and 1122 lines of the source are left out. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
ReplyCnt W_LLVMFuzzerTestOneInput_drain_defs_x W_LLVMFuzzerTestOneInput_drain_calls TopxEntry
W_img_x W_gesture_end W_gestures_end_top AsmTopX CfRBridgeRulesB TopX_RT_lock.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyB3TrPeakCnl.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_send_line_x TopX_RT4 W_errno_azs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require RTx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_cut_x W_LLVMFuzzerTestOneInput_G.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD2l YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcallcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_head_x ReplyLSB ReplyRINVB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcallx YG01cf YG05cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_frame W_frame_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0tcf YG0dcf YG08cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
W_op_add W_LLVMFuzzerTestOneInput_pro W_LLVMFuzzerTestOneInput_pro_x W_LLVMFuzzerTestOneInput_latch_x
W_bx_defs W_LLVMFuzzerTestOneInput_exit_x W_bx_inst W_bx_inst_x YCk0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_sites_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_drain_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_small_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
W_LLVMFuzzerTestOneInput_add W_LLVMFuzzerTestOneInput_add_x W_LLVMFuzzerTestOneInput_write W_LLVMFuzzerTestOneInput_write_x
W_list_push.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
W_LLVMFuzzerTestOneInput_remove W_LLVMFuzzerTestOneInput_remove_x W_LLVMFuzzerTestOneInput_arm_event
W_LLVMFuzzerTestOneInput_event_x TopxImageB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
W_LLVMFuzzerTestOneInput_gone_x W_LLVMFuzzerTestOneInput_gone_base W_LLVMFuzzerTestOneInput_gone_base_x
W_LLVMFuzzerTestOneInput_gone_inst.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0scf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
ReplyLS3B_inst ReplyLSBo YCfn_cf ReplyB3LScnt ReplyB3LScntRP ReplyB3LScntA ReplyB3LScntX ReplyB3GnCnt.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Local Abbreviation segs := (@pa_segs _ fr_prog_listing PB_fr).
Local Abbreviation RPi := CfRBridgeRulesB.RP_cf.
Local Abbreviation dr_cnl_pk := ReplyB3TrPeakCnl.dr_cnl_pk_B.
Local Abbreviation gn_pk := ReplyB3LScnt.pk_gone.
Local Abbreviation LSx CAPS := (ReplyLS3B_inst.LSI TfibB ReplyLSBo.OUT_MAX4 CAPS).
Local Abbreviation RINV := ReplyRINVB.fr_RINV.

Lemma btlsi_LS_cnt_pro : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  forall cx T0 cap out (S2 : astate),
  ReplyCnt.xcnt_ok TfibB (c_S cx) (c_ly cx) (input_blks cx) T0 cap out ->
  ablocks TfibB (c_ly cx) S2 = ablocks TfibB (c_ly cx) (c_S cx) ->
  cnt_ok_pk RPi W_op_add.oa_peak (ablocks TfibB (c_ly cx) S2).
Proof.
  intros rc fx. exact (ReplyB3LScntA.rp_cnt_pro_A TfibB RPi ReplyB3LScntRP.rp_cnt_cf).
Qed.

Lemma btlsi_LS_cnt_exit : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CAPS : lfcx -> Z -> lmod -> alayout -> astate -> Prop),
  forall cx t m ly S (W : world segs) mem,
  LSx CAPS cx t m ly S -> RINV cx t m -> amodel_at TfibB ly S W mem m -> 0 <= t <= OPS_MAX ->
  cnt_ok_pk RPi rf_pk (ablocks TfibB ly S).
Proof.
  intros rc fx CAPS cx t m ly S W mem HL HRI HM Ht.
  apply ReplyLS3B_inst.lsi_parts in HL as (HP & _).
  exact (ReplyB3LScntX.rp_cnt_exit_rf_c TfibB YCfn_cf.CALL_ROOM_B RPi ReplyB3LScntRP.rp_cnt_cf cx t m ly S HP HRI
           (ReplyB3LScntA.msz_ok_of_amodel_at TfibB ly S W mem m HM) Ht).
Qed.

Lemma btlsi_LS_cnt_drain : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CAPS : lfcx -> Z -> lmod -> alayout -> astate -> Prop),
  forall cx t m ly S si h j,
  LSx CAPS cx t m ly S -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.msz_ok m -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  cnt_ok_pk RPi
    (fun P => (Z.to_nat (ReplyCnt.tr_peakP P
       (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)) +
       (dr_cnl_pk h P + 2))%nat)
    (ablocks TfibB ly S).
Proof.
  intros rc fx CAPS cx t m ly S si h j HL HRI Hop Hpick Hj Hfd Heof Hm Ht HU HXP Hoffs.
  apply ReplyLS3B_inst.lsi_parts in HL as (HP & _).
  apply (ReplyB3LScntRP.lsc_rp_of_acnt RPi ReplyB3LScntRP.rp_cnt_cf).
  exact (ReplyB3LScnt.fr_LS3cp_cnt_drain TfibB YCfn_cf.CALL_ROOM_B cx t m ly S si h j HP HRI Hop Hpick Hj Hfd Heof Hm Ht HU
           HXP Hoffs).
Qed.

Lemma btlsi_LS_cnt_add : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CAPS : lfcx -> Z -> lmod -> alayout -> astate -> Prop),
  forall cx t m ly S (W : world segs) mem,
  LSx CAPS cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_add.ad_at_op cx m -> amodel_at TfibB ly S W mem m -> 0 <= t < OPS_MAX ->
  cnt_ok_pk RPi W_op_add.oa_peak (ablocks TfibB ly S).
Proof.
  intros rc fx CAPS cx t m ly S W mem HL HRI Hop HM Ht.
  apply ReplyLS3B_inst.lsi_parts in HL as (HP & _).
  exact (ReplyB3LScntA.rp_cnt_add_A TfibB YCfn_cf.CALL_ROOM_B RPi ReplyB3LScntRP.rp_cnt_cf cx t m ly S W mem HP HRI Hop HM
           Ht).
Qed.

Lemma btlsi_LS_cnt_write : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CAPS : lfcx -> Z -> lmod -> alayout -> astate -> Prop),
  forall cx t m si h ly S (W : world segs) mem,
  LSx CAPS cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_write.wr_pick cx m si h -> 0 < W_LLVMFuzzerTestOneInput_write.wr_n cx m -> amodel_at TfibB ly S W mem m -> 0 <= t < OPS_MAX ->
  cnt_ok_pk RPi (lp_peak (hs_pending h) (W_LLVMFuzzerTestOneInput_write.wr_n cx m)) (ablocks TfibB ly S).
Proof.
  intros rc fx CAPS cx t m si h ly S W mem HL HRI Hpk Hn HM Ht.
  apply ReplyLS3B_inst.lsi_parts in HL as (HP & _).
  exact (ReplyB3LScntA.rp_cnt_write_A TfibB YCfn_cf.CALL_ROOM_B RPi ReplyB3LScntRP.rp_cnt_cf cx t m si h ly S W mem HP HRI
           Hpk Hn HM Ht).
Qed.

Lemma btlsi_LS_cnt_remove : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CAPS : lfcx -> Z -> lmod -> alayout -> astate -> Prop),
  forall cx t m ly S (W : world segs) mem si h j0,
  LSx CAPS cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> amodel_at TfibB ly S W mem m -> 0 <= t < OPS_MAX ->
  cnt_ok_pk RPi (W_LLVMFuzzerTestOneInput_remove_x.rm_pk m h j0) (ablocks TfibB ly S).
Proof.
  intros rc fx CAPS cx t m ly S W mem si h j0 HL HRI Hat HM Ht.
  apply ReplyLS3B_inst.lsi_parts in HL as (HP & _).
  exact (ReplyB3LScntA.rp_cnt_rm_A TfibB YCfn_cf.CALL_ROOM_B RPi ReplyB3LScntRP.rp_cnt_cf cx t m ly S W mem si h j0 HP HRI
           Hat HM Ht).
Qed.

Lemma btlsi_LS_cnt_event : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CAPS : lfcx -> Z -> lmod -> alayout -> astate -> Prop),
  forall cx t m ly S e,
  LSx CAPS cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_arm_event.ev_evt cx m e ->
  Forall (fun e0 => 0 <= re_cap e0 <= 16384 /\
    Forall (fun k => Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e0)) (lm_es m) /\
  Forall (fun o => match o with
                   | Some h => Forall (fun r => Z.of_nat (length (snd r)) <= APARTIAL) (hl_recs (hs_expected h)) /\
                               Forall (fun r => Z.of_nat (length (snd r)) <= APARTIAL) (hl_recs (hs_held h))
                   | None => True end) (lm_hs m) ->
  0 <= t < OPS_MAX ->
  (ReplyCnt.acnt (rp_Psec RPi) (ablocks TfibB ly S) + ((if rp_Psec RPi (re_len e) then 1 else 0) + 2) <= rp_Lsec RPi)%nat /\
  (ReplyCnt.acnt (rp_P24 RPi) (ablocks TfibB ly S) + ((if rp_P24 RPi (re_len e) then 1 else 0) + 2) <= rp_L24 RPi)%nat /\
  (forall c, 1 <= c <= 30 ->
     (ReplyCnt.acnt (rp_Pcls RPi c) (ablocks TfibB ly S) + ((if rp_Pcls RPi c (re_len e) then 1 else 0) + 2)
        <= rp_LPRIM RPi c)%nat).
Proof.
  intros rc fx CAPS cx t m ly S e HL HRI He Hm Ht.
  apply ReplyLS3B_inst.lsi_parts in HL as (HP & _).
  destruct ReplyB3LScntRP.rp_cnt_cf as (E1 & E2 & E3 & E4 & E5 & E6).
  rewrite E1, E2, E3, E4, E5, E6.
  exact (ReplyB3LScnt.fr_LS3cp_cnt_event TfibB YCfn_cf.CALL_ROOM_B cx t m ly S e HP HRI He Hm Ht).
Qed.

Lemma btlsi_CNT_gone_rig : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  W_LLVMFuzzerTestOneInput_gone_base.GN_CNT_rig gn_pk (fun cx m hs =>
  rig_pk (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (W_LLVMFuzzerTestOneInput_gone_base.gn_id cx m)
    (lm_es m) hs)).
Proof. intros rc fx. exact ReplyB3GnCnt.gcnt_rig. Qed.

Lemma btlsi_LS_cnt_gone : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CAPS : lfcx -> Z -> lmod -> alayout -> astate -> Prop),
  W_LLVMFuzzerTestOneInput_gone_base_x.GN_LS_cnt_x TfibB (LSx CAPS) RINV RPi gn_pk.
Proof.
  intros rc fx CAPS. unfold W_LLVMFuzzerTestOneInput_gone_base_x.GN_LS_cnt_x.
  intros cx t m ly S hs HL HRI Hgp Hm Ht HU Hpos Hoff.
  apply ReplyLS3B_inst.lsi_parts in HL as (HP & _).
  apply (ReplyB3LScntRP.lsc_rp_of_acnt RPi ReplyB3LScntRP.rp_cnt_cf).
  exact (ReplyB3LScnt.fr_LS3cp_cnt_gone TfibB YCfn_cf.CALL_ROOM_B cx t m ly S hs HP HRI Hgp Hm Ht HU Hpos Hoff).
Qed.

Lemma btlsi_CNT_gone_step : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  W_LLVMFuzzerTestOneInput_gone_base.GN_CNT_step RINV gn_pk
  (fun h => cnl_pk (hs_expected h) (hs_held h)).
Proof. intros rc fx. exact ReplyB3GnCnt.gcnt_step. Qed.
