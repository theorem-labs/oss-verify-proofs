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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_write
W_LLVMFuzzerTestOneInput_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT ListTr drain_b_c send_line_b_c gesture_end_b_c gestures_end_b_c gesture_end_c relay_remove_b_c RelayCap
  SlotReads SlotInv SlotDrain3Aux SlotPass2Aux relay_remove_b_aux.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require PresetRoom.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB ReplyRINVB ReplyLSBArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBDrainPre ReplyLSBTrPeak.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3Base ReplyB3LS3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3LS3Arms ReplyLSCntL ReplyB3LS3c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3LS3cArms ReplyTrPeakW.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3LSCntM ReplyB3LS3p ReplyB3TrPeakCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3TrPeakCntR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3LScnt ReplyB3LScntRP.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_remove
  W_LLVMFuzzerTestOneInput_remove_x.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Notation wr_n := W_LLVMFuzzerTestOneInput_write.wr_n.
Local Notation wr_pick := W_LLVMFuzzerTestOneInput_write.wr_pick.
Local Notation ad_at_op := W_LLVMFuzzerTestOneInput_add.ad_at_op.

Section sz.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.

Lemma lsc_alist_texts : forall ly S (W : world segs) mem LA l,
  alist_at B ly S W mem LA l true -> ReplyCnt.texts_ok l.
Proof.
  intros ly S W mem LA l (_ & _ & _ & _ & _ & _ & _ & _ & HF). unfold ReplyCnt.texts_ok.
  eapply Forall_impl; [|exact HF]. intros r (_ & _ & Ht & _). exact (proj2 (Ht eq_refl)).
Qed.
Lemma lsc_asrc_texts : forall ly S (W : world segs) mem HA h,
  asrc_at B ly S W mem HA h -> ReplyCnt.texts_ok (hs_expected h) /\ ReplyCnt.texts_ok (hs_held h).
Proof.
  intros ly S W mem HA h
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & He & Hh & _).
  exact (conj (lsc_alist_texts _ _ _ _ _ _ He) (lsc_alist_texts _ _ _ _ _ _ Hh)).
Qed.
Lemma lsc_entry_sz : forall ly S (W : world segs) mem e, aentry_ok B ly S W mem e ->
  0 <= re_cap e <= 16384 /\
  Forall (fun k => Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e).
Proof.
  intros ly S W mem e (_ & _ & _ & _ & _ & Hcap & _ & _ & _ & _ & _ & _ & _ & _ & HK). split; [lia|].
  eapply Forall_impl; [|exact HK]. intros k (_ & _ & _ & Hk). lia.
Qed.
Lemma msz_es_of_amodel_at : forall ly S (W : world segs) mem m, amodel_at B ly S W mem m ->
  Forall (fun e => 0 <= re_cap e <= 16384 /\
    Forall (fun k => Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e)) (lm_es m).
Proof.
  intros ly S W mem m (_ & _ & Hrel & _). destruct Hrel as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HF & _).
  eapply Forall_impl; [|exact HF]. intros e He. exact (lsc_entry_sz _ _ _ _ e He).
Qed.
Lemma msz_hs_of_amodel_at : forall ly S (W : world segs) mem m, amodel_at B ly S W mem m ->
  Forall (fun o => match o with Some h => ReplyCnt.texts_ok (hs_expected h) /\ ReplyCnt.texts_ok (hs_held h)
                   | None => True end) (lm_hs m).
Proof.
  intros ly S W mem m (Hlen & Hsl & _). apply Forall_forall. intros o Ho.
  destruct (In_nth (lm_hs m) o None Ho) as (i & Hi & Ei). rewrite Hlen in Hi.
  specialize (Hsl i Hi). rewrite Ei in Hsl. destruct o as [h|]; [|exact I].
  exact (lsc_asrc_texts _ _ _ _ _ h Hsl).
Qed.
Lemma msz_ok_of_amodel_at : forall ly S (W : world segs) mem m, amodel_at B ly S W mem m ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m).
Proof.
  intros ly S W mem m H.
  split; [exact (msz_es_of_amodel_at ly S W mem m H) | exact (msz_hs_of_amodel_at ly S W mem m H)].
Qed.
End sz.

Section arms.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable CALL_ROOM_B : Z.
Variable RP : roomp.
Hypothesis HRP_CNT : RP_CNT RP.
#[local] Notation LSx := (fr_LS3cp B CALL_ROOM_B).
#[local] Notation RINV := fr_RINV.

Lemma rp_cnt_pro_A : forall cx T0 cap out (S2 : astate),
  ReplyCnt.xcnt_ok B (c_S cx) (c_ly cx) (input_blks cx) T0 cap out ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) ->
  cnt_ok_pk RP W_op_add.oa_peak (ablocks B (c_ly cx) S2).
Proof.
  intros cx T0 cap out S2 HX E.
  exact (rp_cnt_pro B RP HRP_CNT (c_S cx) S2 (c_ly cx) (c_p cx) (c_n cx) T0 cap out HX E).
Qed.
Lemma rp_cnt_add_A : forall cx t m ly S (W : world segs) mem,
  LSx cx t m ly S -> RINV cx t m -> ad_at_op cx m -> amodel_at B ly S W mem m -> 0 <= t < OPS_MAX ->
  cnt_ok_pk RP oa_peak (ablocks B ly S).
Proof.
  intros cx t m ly S W mem HLS HRI Hop HM Ht.
  exact (rp_cnt_add B CALL_ROOM_B RP HRP_CNT cx t m ly S HLS HRI Hop (msz_ok_of_amodel_at B ly S W mem m HM) Ht).
Qed.
Lemma rp_cnt_write_A : forall cx t m si h ly S (W : world segs) mem,
  LSx cx t m ly S -> RINV cx t m -> wr_pick cx m si h -> 0 < wr_n cx m -> amodel_at B ly S W mem m -> 0 <= t < OPS_MAX ->
  cnt_ok_pk RP (lp_peak (hs_pending h) (wr_n cx m)) (ablocks B ly S).
Proof.
  intros cx t m si h ly S W mem HLS HRI Hpk Hn HM Ht.
  exact (rp_cnt_write B CALL_ROOM_B RP HRP_CNT cx t m si h (wr_n cx m) ly S HLS HRI Hpk Hn
           (msz_ok_of_amodel_at B ly S W mem m HM) Ht).
Qed.
Lemma rp_cnt_rm_A : forall cx t m ly S (W : world segs) mem si h j0,
  LSx cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  amodel_at B ly S W mem m -> 0 <= t < OPS_MAX ->
  cnt_ok_pk RP (W_LLVMFuzzerTestOneInput_remove_x.rm_pk m h j0) (ablocks B ly S).
Proof.
  intros cx t m ly S W mem si h j0 HLS HRI Hat HM Ht.
  pose proof Hat as (_ & _ & _ & _ & _ & Hh & Hj0 & _).
  destruct (W_LLVMFuzzerTestOneInput_remove.rm_mfacts_of B ly S W mem m HM) as (Hpos & _ & Hoffs).
  assert (HU : Z.of_nat (length (re_U (nth j0 (lm_es m) relay_remove_b_c.no_entry))) <= APARTIAL).
  { pose proof HM as (_ & _ & HREL & _).
    destruct HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HAE & _). rewrite Forall_forall in HAE.
    destruct (HAE _ (nth_In (lm_es m) relay_remove_b_c.no_entry Hj0)) as (_ & _ & _ & _ & _ & _ & U1 & U2 & _).
    lia. }
  exact (rp_cnt_rm B CALL_ROOM_B RP HRP_CNT cx t m ly S si h j0 HLS HRI Hat (msz_ok_of_amodel_at B ly S W mem m HM) Ht HU
           Hpos (Hoffs si h Hh)).
Qed.
End arms.
