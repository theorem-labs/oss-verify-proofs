(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_LLVMFuzzerTestOneInput_top_x.v, with its module paths and module names changed; 104 of its 167 lines of code are new or changed and 1164 lines of the source are left out. *)
(* top_x's COUNT rows (W_LLVMFuzzerTestOneInput_top_x.v at the TOP head 3d17f490d56), each at top_x's exact text with
   LSx := ReplyLSI.LSI B OM nsec KMAX KC, RINV := fr_RINV, TfibB := B and RP := RPi (top_x's CfRBridgeRules.RP_cf, whose
   count fields are ReplyCnt.v's: ReplyLScntRP.rp_cnt_cf).  proves no function (kind: invariant lemma).
   Each is proved from s5-r1d's rows by projecting LSI to its first part fr_LS3cp B:
   - lsi_cnt_pro / _add / _write / _remove: ReplyLScntA.v rp_cnt_pro_A / rp_cnt_add_A / rp_cnt_write_A / rp_cnt_rm_A;
   - lsi_cnt_event / _drain / _gone: ReplyLScnt.v fr_LS3cp_cnt_event / fr_LS3cp_cnt_drain / fr_LS3cp_cnt_gone through
     ReplyLScntRP.v lsc_rp_of_acnt (the event row's text names RPi's fields, rewritten by rp_cnt_cf);
   - lsi_cnt_exit: ReplyLScntX.v rp_cnt_exit_rf_c over the closed range 0 <= t <= OPS_MAX, its msz_ok from amodel_at
     (ReplyLScntA.v msz_ok_of_amodel_at);
   - lsi_cnt_gone_rig / lsi_cnt_gone_step: ReplyGnCnt.v gcnt_rig / gcnt_step (they name no LS).
   Not here (not s5-r1d's rows): LS_exit_cnt and LS_exit_cap (s5-r9), DR_CNT_grow / DR_CNT_cnl and RM_CNT_cnl /
   RM_CNT_cshe / RM_CNT_sr (s5-spd). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_drain.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_write.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_event.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyRINV.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLSArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  drain_b_c gestures_end_b_c gesture_end_c relay_remove_b_c RelayCap SlotReads SlotInv SlotDrain3Aux SlotPass2Aux
  relay_remove_b_aux send_line_b_c RelayRunT RelayRunF ListTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ACfn_cf CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLS3 ReplyLSDrainPre ReplyLSDrain3 ReplyLSRemove3 ReplyLSEvent3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3Arms ReplyLSCntL ReplyLS3c ReplyLS3cArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyTrPeak ReplyTrPeakC.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_exit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3p ReplyLS3oRf ReplyLS3oGn ReplyLS3e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_gone_base.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLS3cTopxGoneF ReplyLS3cTopxGoneH ReplyLS3cTopx ReplyLS3cTopxPost ReplyLS3cTopxPro
  ReplyLS3cTopxGone8.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3Peak ReplyLS3pGn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyLS3eCap.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_LLVMFuzzerTestOneInput_remove.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyLSI.
(* the count rows and the names top_x's count texts use, Required without Import (cited qualified) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require
  ReplyLScnt ReplyLScntRP ReplyLScntA ReplyLScntX ReplyGnCnt ReplyTrPeakCnl CfRBridgeRules W_contract_x
  W_LLVMFuzzerTestOneInput_drain_x W_LLVMFuzzerTestOneInput_remove_x W_LLVMFuzzerTestOneInput_gone_base_x.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.


Section cnt.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable OM : Z.
(* the counting meter's parameters (ReplyLSI.v); the count rows do not read fr_SEC *)
Variable nsec : astate -> Z.
Variables KMAX KC : Z.
Local Notation LSx := (ReplyLSI.LSI B OM nsec KMAX KC).
Local Notation RINV := fr_RINV.
Local Notation TfibB := B.
Local Notation RPi := CfRBridgeRules.RP_cf.

(* top_x :428 LS_cnt_pro (it names no LS) *)
Lemma lsi_cnt_pro : forall cx T0 cap out (S2 : astate),
  ReplyCnt.xcnt_ok TfibB (c_S cx) (c_ly cx) (input_blks cx) T0 cap out ->
  ablocks TfibB (c_ly cx) S2 = ablocks TfibB (c_ly cx) (c_S cx) ->
  cnt_ok_pk RPi W_op_add.oa_peak (ablocks TfibB (c_ly cx) S2).
Proof. exact (ReplyLScntA.rp_cnt_pro_A B RPi ReplyLScntRP.rp_cnt_cf). Qed.
(* top_x :266 LS_cnt_add *)
Lemma lsi_cnt_add : forall cx t m ly S (W : world segs) mem,
  LSx cx t m ly S -> RINV cx t m -> ad_at_op cx m -> amodel_at TfibB ly S W mem m -> 0 <= t < OPS_MAX ->
  cnt_ok_pk RPi W_op_add.oa_peak (ablocks TfibB ly S).
Proof.
  intros cx t m ly S W mem (HP & _) HRI Hop HM Ht.
  exact (ReplyLScntA.rp_cnt_add_A B RPi ReplyLScntRP.rp_cnt_cf cx t m ly S W mem HP HRI Hop HM Ht).
Qed.
(* top_x :303 LS_cnt_write *)
Lemma lsi_cnt_write : forall cx t m si h ly S (W : world segs) mem,
  LSx cx t m ly S -> RINV cx t m -> wr_pick cx m si h -> 0 < wr_n cx m -> amodel_at TfibB ly S W mem m -> 0 <= t < OPS_MAX ->
  cnt_ok_pk RPi (W_contract_x.lp_peak (hs_pending h) (wr_n cx m)) (ablocks TfibB ly S).
Proof.
  intros cx t m si h ly S W mem (HP & _) HRI Hpk Hn HM Ht.
  exact (ReplyLScntA.rp_cnt_write_A B RPi ReplyLScntRP.rp_cnt_cf cx t m si h ly S W mem HP HRI Hpk Hn HM Ht).
Qed.
(* top_x :362 LS_cnt_event (ReplyLScnt.fr_LS3cp_cnt_event, its guard msz_ok written out) *)
Lemma lsi_cnt_event : forall cx t m ly S e,
  LSx cx t m ly S -> RINV cx t m -> ev_evt cx m e ->
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
  intros cx t m ly S e (HP & _) HRI He Hm Ht.
  destruct ReplyLScntRP.rp_cnt_cf as (E1 & E2 & E3 & E4 & E5 & E6).
  rewrite E1, E2, E3, E4, E5, E6.
  exact (ReplyLScnt.fr_LS3cp_cnt_event B cx t m ly S e HP HRI He Hm Ht).
Qed.
(* top_x :605 LS_cnt_drain (ReplyLScnt.fr_LS3cp_cnt_drain: its peak pk_drain, check_no_loss's part dr_cnl_pk :=
   ReplyTrPeakCnl.cnl_pk; the guard is _drain_x.v's msz_ok m) *)
Lemma lsi_cnt_drain : forall cx t m ly S si h j,
  LSx cx t m ly S -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  W_LLVMFuzzerTestOneInput_drain_x.msz_ok m -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  cnt_ok_pk RPi
    (fun P => (Z.to_nat (ReplyCnt.tr_peakP P
       (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)) +
       (ReplyTrPeakCnl.cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) P + 2))%nat)
    (ablocks TfibB ly S).
Proof.
  intros cx t m ly S si h j (HP & _) HRI Hop Hpick Hj Hfd Heof Hm Ht HU HXP Hoffs.
  apply (ReplyLScntRP.lsc_rp_of_acnt RPi ReplyLScntRP.rp_cnt_cf).
  exact (ReplyLScnt.fr_LS3cp_cnt_drain B cx t m ly S si h j HP HRI Hop Hpick Hj Hfd Heof Hm Ht HU HXP Hoffs).
Qed.
(* top_x :674 LS_cnt_exit, over the closed range 0 <= t <= OPS_MAX (ReplyLScntX.rp_cnt_exit_rf_c) *)
Lemma lsi_cnt_exit : forall cx t m ly S (W : world segs) mem,
  LSx cx t m ly S -> RINV cx t m -> amodel_at TfibB ly S W mem m -> 0 <= t <= OPS_MAX ->
  cnt_ok_pk RPi W_contract_x.rf_pk (ablocks TfibB ly S).
Proof.
  intros cx t m ly S W mem (HP & _) HRI HM Ht.
  exact (ReplyLScntX.rp_cnt_exit_rf_c B RPi ReplyLScntRP.rp_cnt_cf cx t m ly S HP HRI
           (ReplyLScntA.msz_ok_of_amodel_at B ly S W mem m HM) Ht).
Qed.
(* top_x :782 LS_cnt_remove (ReplyLScntA.rp_cnt_rm_A) *)
Lemma lsi_cnt_remove : forall cx t m ly S (W : world segs) mem si h j0,
  LSx cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> amodel_at TfibB ly S W mem m -> 0 <= t < OPS_MAX ->
  cnt_ok_pk RPi (W_LLVMFuzzerTestOneInput_remove_x.rm_pk m h j0) (ablocks TfibB ly S).
Proof.
  intros cx t m ly S W mem si h j0 (HP & _) HRI Hat HM Ht.
  exact (ReplyLScntA.rp_cnt_rm_A B RPi ReplyLScntRP.rp_cnt_cf cx t m ly S W mem si h j0 HP HRI Hat HM Ht).
Qed.
(* top_x :844 LS_cnt_gone: gone_base_x's GN_LS_cnt_x at gn_pk := ReplyLScnt.pk_gone (ReplyLScnt.fr_LS3cp_cnt_gone) *)
Lemma lsi_cnt_gone :
  W_LLVMFuzzerTestOneInput_gone_base_x.GN_LS_cnt_x TfibB LSx RINV RPi ReplyLScnt.pk_gone.
Proof.
  unfold W_LLVMFuzzerTestOneInput_gone_base_x.GN_LS_cnt_x.
  intros cx t m ly S hs (HP & _) HRI Hgp Hm Ht HU Hpos Hoff.
  apply (ReplyLScntRP.lsc_rp_of_acnt RPi ReplyLScntRP.rp_cnt_cf).
  exact (ReplyLScnt.fr_LS3cp_cnt_gone B cx t m ly S hs HP HRI Hgp Hm Ht HU Hpos Hoff).
Qed.
(* top_x :841 CNT_gone_rig (ReplyGnCnt.gcnt_rig; its gn_rig_pk_x is this function) *)
Lemma lsi_cnt_gone_rig : W_LLVMFuzzerTestOneInput_gone_base.GN_CNT_rig ReplyLScnt.pk_gone (fun cx m hs =>
  W_contract_x.rig_pk (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
    (W_LLVMFuzzerTestOneInput_gone_base.gn_id cx m) (lm_es m) hs)).
Proof. exact ReplyGnCnt.gcnt_rig. Qed.
(* top_x :845 CNT_gone_step (ReplyGnCnt.gcnt_step; its gn_cnl_pk_x is this function) *)
Lemma lsi_cnt_gone_step : W_LLVMFuzzerTestOneInput_gone_base.GN_CNT_step RINV ReplyLScnt.pk_gone
  (fun h => W_contract_x.cnl_pk (hs_expected h) (hs_held h)).
Proof. exact ReplyGnCnt.gcnt_step. Qed.
End cnt.
