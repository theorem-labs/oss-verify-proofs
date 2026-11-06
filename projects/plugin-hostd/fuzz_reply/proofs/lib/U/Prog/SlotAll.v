From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract ContractT FrameAPI SlotKept
  AllocPack3 SlotPack3 FrameProof.
From OSSVerify.plugin_hostd.fuzz_reply Require Statements.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import StatementKept SlotInv SlotSteps SlotRes
  SlotLoop SlotCaps3 SlotRI3 SlotEntryRun SlotEntry SlotPass0 SlotPass1 SlotPass1w SlotPass7P SlotPass9
  SlotResReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import check_bounded_c check_shape_event_c
  check_shape_done_c next_line_c strnlen_c memcpy_c memchr_c memmove_c memset_c strlen_c bcmp_c __errno_location_c
  pthread_mutex_lock_c pthread_mutex_unlock_c wake_c op_add_c source_reset_c list_free_c relay_add_b_c list_push_c
  send_line_b_c relay_event_b_c gesture_end_b_c gestures_end_b_c relay_finish_b_c list_find_c has_prefix_c
  check_shape_ends_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import check_bounded check_shape_event
  check_shape_done next_line strnlen memcpy memchr memmove memset strlen bcmp __errno_location pthread_mutex_lock
  pthread_mutex_unlock wake op_add source_reset list_free relay_add_b list_push send_line_b relay_event_b
  gesture_end_b gestures_end_b relay_finish_b list_find has_prefix check_shape_ends.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import SlotExitMove SlotExitFin SlotExitScan
  SlotExit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import drain_b_c strndup_rt strrchr_c strcmp_c
  memrchr_c strncmp_c drain_b strrchr strcmp memrchr strncmp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import relay_remove_b_c check_no_loss_c
  check_no_loss_read_c memcpy_same_c gesture_model_c list_drop_c relay_remove_b check_no_loss check_no_loss_read
  memcpy_same gesture_model list_drop SlotPass4 SlotPass2 SlotPass2P.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import snprintf_c snprintf relay_source_c
  relay_source relay_reads_c relay_reads SlotP2Res3 SlotP4Res3 SlotP5Res3 SlotP5Res3Full SlotPass5V SlotPass5V2
  SlotPass5G SlotPass5C SlotPass5.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require relay_instance_gone_b.
Import ListNotations.
Local Open Scope Z_scope.

Lemma frame_contracts : forall B API LS SH SK ra empty rc fx, frame_facts B API LS SH SK ra empty ->
  @op_add_contract fx rc B (API rc) pack3_form /\ @list_push_contract fx rc B (API rc) pack3_form /\
  (@malloc_contract_rt fx rc B (API rc) pack3_form /\ @free_contract_rt fx rc B (API rc) pack3_form /\
   @relay_event_contract fx rc B (API rc) pack3_form).
Proof.
  intros B API LS SH SK ra empty rc fx
    (SEG & RA2 & HMAL & HFREE & HREAL & HCAL & HERR & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 &
     F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27 & F28 & F29 & F30 & F31 & FA).
  destruct (FA rc fx) as (MAL & FRE & FNC & REAL & CAL & SLK & CTX & LOW & NDP & BW & EU & GRW & AX & NG & NR).
  destruct (REAL 0x178f8 HREAL) as [RAC RNC].
  pose proof (HERR rc) as ERR.
  pose proof (memmove_holds memcpy_holds) as MMV.
  assert (LDC : @list_drop_contract fx rc B (API rc) pack3_form) by (apply list_drop_holds; assumption).
  assert (LFR : @list_free_contract fx rc B (API rc) pack3_form) by (apply list_free_holds; assumption).
  assert (SRS : @source_reset_contract fx rc B (API rc) pack3_form)
    by (apply source_reset_holds; first [assumption | exact memset_holds]).
  assert (RAD : @relay_add_contract fx rc B (API rc) pack3_form)
    by (apply relay_add_holds; first [assumption | exact pthread_mutex_lock_holds | exact pthread_mutex_unlock_holds |
                                      exact memset_holds | exact wake_holds]).
  assert (SLC : @send_line_contract fx rc B (API rc) pack3_form)
    by (apply send_line_holds; first [assumption | exact memcpy_holds | exact __errno_location_holds]).
  split; [apply op_add_holds; assumption|].
  split; [apply list_push_holds; first [assumption | exact memcpy_holds]|].
  split; [exact MAL|]. split; [exact FRE|].
  apply relay_event_holds; first [assumption | exact pthread_mutex_lock_holds | exact pthread_mutex_unlock_holds |
                                  exact strlen_holds].
Qed.

Lemma exit_contracts : forall B API LS SH SK ra empty rc fx, frame_facts B API LS SH SK ra empty ->
  @relay_finish_contract fx rc B (API rc) pack3_form /\ @check_shape_ends_contract fx rc B (API rc) pack3_form /\
  @source_reset_contract fx rc B (API rc) pack3_form.
Proof.
  intros B API LS SH SK ra empty rc fx
    (SEG & RA2 & HMAL & HFREE & HREAL & HCAL & HERR & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 &
     F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27 & F28 & F29 & F30 & F31 & FA).
  destruct (FA rc fx) as (MAL & FRE & FNC & REAL & CAL & SLK & CTX & LOW & NDP & BW & EU & GRW & AX & NG & NR).
  destruct (REAL 0x178f8 HREAL) as [RAC RNC].
  pose proof (HERR rc) as ERR.
  pose proof (memmove_holds memcpy_holds) as MMV.
  assert (LDC : @list_drop_contract fx rc B (API rc) pack3_form) by (apply list_drop_holds; assumption).
  assert (LFR : @list_free_contract fx rc B (API rc) pack3_form) by (apply list_free_holds; assumption).
  assert (SLC : @send_line_contract fx rc B (API rc) pack3_form)
    by (apply send_line_holds; first [assumption | exact memcpy_holds | exact __errno_location_holds]).
  assert (GEC : @gesture_end_contract fx rc B (API rc) pack3_form)
    by (apply gesture_end_holds; first [assumption | exact strlen_holds]).
  assert (GSC : @gestures_end_contract fx rc B (API rc) pack3_form) by (apply gestures_end_holds; assumption).
  split; [apply relay_finish_holds; first [assumption | exact pthread_mutex_lock_holds |
                                           exact pthread_mutex_unlock_holds]|].
  split; [apply check_shape_ends_holds; first [assumption | exact (next_line_holds memchr_holds) |
                                               exact (list_find_holds bcmp_holds) |
                                               exact (has_prefix_holds strlen_holds bcmp_holds)]|].
  apply source_reset_holds; first [assumption | exact memset_holds].
Qed.

Lemma drain_contracts : forall B API LS SH SK ra empty rc fx, frame_facts B API LS SH SK ra empty ->
  @drain_contract fx rc B (API rc) pack3_form.
Proof.
  intros B API LS SH SK ra empty rc fx
    (SEG & RA2 & HMAL & HFREE & HREAL & HCAL & HERR & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 &
     F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27 & F28 & F29 & F30 & F31 & FA).
  destruct (FA rc fx) as (MAL & FRE & FNC & REAL & CAL & SLK & CTX & LOW & NDP & BW & EU & GRW & AX & NG & NR).
  destruct (REAL 0x178f8 HREAL) as [RAC RNC].
  pose proof (HERR rc) as ERR.
  pose proof (memmove_holds memcpy_holds) as MMV.
  assert (SLC : @send_line_contract fx rc B (API rc) pack3_form)
    by (apply send_line_holds; first [assumption | exact memcpy_holds | exact __errno_location_holds]).
  assert (LPC : @list_push_contract fx rc B (API rc) pack3_form)
    by (apply list_push_holds; first [assumption | exact memcpy_holds]).
  assert (LDC : @list_drop_contract fx rc B (API rc) pack3_form) by (apply list_drop_holds; assumption).
  pose proof (strndup_holds_rt B (API rc) SEG HMAL ERR pack3_form MAL (strnlen_holds memchr_holds) memcpy_holds)
    as SDC.
  exact (drain_holds B (API rc) pack3_form AX CTX SLK BW EU HFREE NDP RAC RNC __errno_location_holds SLC LPC SDC FRE
    memchr_holds MMV memcpy_holds (strrchr_holds strlen_holds memrchr_holds) strcmp_holds strncmp_holds strlen_holds
    LDC).
Qed.

Lemma p4_contracts : forall B API LS SH SK ra empty rc fx, frame_facts B API LS SH SK ra empty ->
  @relay_remove_contract fx rc B (API rc) pack3_form /\ @check_no_loss_contract fx rc B (API rc) pack3_form /\
  @check_shape_ends_contract fx rc B (API rc) pack3_form /\ @source_reset_contract fx rc B (API rc) pack3_form.
Proof.
  intros B API LS SH SK ra empty rc fx HF.
  pose proof (drain_contracts B API LS SH SK ra empty rc fx HF) as DRC.
  destruct (exit_contracts B API LS SH SK ra empty rc fx HF) as (_ & CSE & SRS).
  destruct HF as (SEG & RA2 & HMAL & HFREE & HREAL & HCAL & HERR & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 &
    F17 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27 & F28 & F29 & F30 & F31 & FA).
  destruct (FA rc fx) as (MAL & FRE & FNC & REAL & CAL & SLK & CTX & LOW & NDP & BW & EU & GRW & AX & NG & NR).
  destruct (REAL 0x178f8 HREAL) as [RAC RNC].
  pose proof (HERR rc) as ERR.
  pose proof (memmove_holds memcpy_holds) as MMV.
  assert (SLC : @send_line_contract fx rc B (API rc) pack3_form)
    by (apply send_line_holds; first [assumption | exact memcpy_holds | exact __errno_location_holds]).
  assert (GEC : @gesture_end_contract fx rc B (API rc) pack3_form)
    by (apply gesture_end_holds; first [assumption | exact strlen_holds]).
  assert (GSC : @gestures_end_contract fx rc B (API rc) pack3_form) by (apply gestures_end_holds; assumption).
  assert (LPC : @list_push_contract fx rc B (API rc) pack3_form)
    by (apply list_push_holds; first [assumption | exact memcpy_holds]).
  assert (LDC : @list_drop_contract fx rc B (API rc) pack3_form) by (apply list_drop_holds; assumption).
  assert (GMC : @gesture_model_contract fx rc B (API rc) pack3_form)
    by (apply gesture_model_holds; first [assumption | exact bcmp_holds | exact (list_find_holds bcmp_holds)]).
  split; [apply relay_remove_holds; first [assumption | exact memcpy_holds | exact memcpy_same_holds |
                                           exact pthread_mutex_lock_holds | exact pthread_mutex_unlock_holds |
                                           exact wake_holds]|].
  split; [apply check_no_loss_holds; first [assumption | exact (next_line_holds memchr_holds) | exact bcmp_holds]|].
  split; [exact CSE|exact SRS].
Qed.

Lemma p5_contracts : forall B API LS SH SK ra empty rc fx, frame_facts B API LS SH SK ra empty ->
  @check_no_loss_contract fx rc B (API rc) pack3_form /\ @check_shape_ends_contract fx rc B (API rc) pack3_form.
Proof.
  intros B API LS SH SK ra empty rc fx HF.
  destruct (p4_contracts B API LS SH SK ra empty rc fx HF) as (_ & CNL & CSE & _).
  split; assumption.
Qed.

(* h-relay-2's relay_instance_gone_p_holds, its callee contracts discharged as in exit_contracts/drain_contracts. *)
Lemma gone_partial_reply_holds : forall B API LS SH SK ra empty rc, frame_facts B API LS SH SK ra empty ->
  gone_partial_S rc B (API rc).
Proof.
  intros B API LS SH SK ra empty rc HF. unfold gone_partial_S. intros fx.
  assert (DRC : forall fx' : YK11.FPState, @drain_contract fx' rc B (API rc) pack3_form)
    by (intros fx'; exact (drain_contracts B API LS SH SK ra empty rc fx' HF)).
  destruct HF as (SEG & RA2 & HMAL & HFREE & HREAL & HCAL & HERR & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 &
    F17 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27 & F28 & F29 & F30 & F31 & FA).
  assert (FRC : forall fx' : YK11.FPState, @free_contract_rt fx' rc B (API rc) pack3_form)
    by (intros fx'; destruct (FA rc fx') as (_ & FR & _); exact FR).
  assert (GEC : forall fx' : YK11.FPState, @gesture_end_contract fx' rc B (API rc) pack3_form).
  { intros fx'.
    destruct (FA rc fx') as (MAL & FRE & FNC & REAL & CAL & SLK & CTX & LOW & NDP & BW & EU & GRW & AX & NG & NR).
    destruct (REAL 0x178f8 HREAL) as [RAC RNC].
    pose proof (HERR rc) as ERR.
    assert (SLC : @send_line_contract fx' rc B (API rc) pack3_form)
      by (apply send_line_holds; first [assumption | exact memcpy_holds | exact __errno_location_holds]).
    apply gesture_end_holds; first [assumption | exact strlen_holds]. }
  destruct (FA rc fx) as (MAL & FRE & FNC & REAL & CAL & SLK & CTX & LOW & NDP & BW & EU & GRW & AX & NG & NR).
  apply (@relay_instance_gone_b.relay_instance_gone_p_holds fx rc B (API rc));
    first [assumption | exact HFREE | exact pthread_mutex_lock_holds | exact pthread_mutex_unlock_holds |
           exact snprintf_holds | exact strlen_holds | exact strncmp_holds].
Qed.

Theorem fuzz_reply_slot_parts : fuzz_reply_slot_p3 CS_reply frame_MCAP.
Proof.
  apply (slot_of_steps CS_reply RI3_reply).
  - exact (entry_holds CS_reply RI3_reply pack3_form RI3_start_ok entry_res_reply_s
      (fun B API LS SH SK ra empty rc fx HF => proj1 (frame_contracts B API LS SH SK ra empty rc fx HF))).
  - intros op Hop.
    assert (H : op = 0 \/ op = 1 \/ op = 2 \/ op = 3 \/ op = 4 \/ op = 5 \/ op = 6 \/ op = 7 \/ op = 8 \/ op = 9) by lia.
    destruct H as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]].
    + exact (pass0_holds check_bounded_holds
        (fun B API LS SH SK ra empty rc fx HF => proj1 (frame_contracts B API LS SH SK ra empty rc fx HF))
        RI3_reply RI3_mono op0_res_reply_s).
    + exact (pass1_holds pack3_form check_bounded_holds
        (fun B API LS SH SK ra empty HF rc fx => proj1 (proj2 (frame_contracts B API LS SH SK ra empty rc fx HF)))
        RI3_reply RI3_mono push_res_reply_s).
    + exact (pass2_holds pack3_form check_bounded_holds pthread_mutex_lock_holds pthread_mutex_unlock_holds
        drain_contracts check_no_loss_read_holds
        (fun B API LS SH SK ra empty rc fx HF => proj1 (proj2 (p4_contracts B API LS SH SK ra empty rc fx HF)))
        check_shape_done_holds RI3_reply RI3_mono p2_drain_res3 p2_cnl_res3).
    + exact (pass3_holds check_bounded_holds RI3_reply RI3_mono).
    + exact (pass4_holds pack3_form check_bounded_holds check_no_loss_read_holds check_shape_done_holds
        p4_contracts RI3_reply RI3_mono p4_res3).
    + exact (pass5_holds snprintf_holds (relay_reads_holds relay_source_holds) check_no_loss_read_holds
        check_bounded_holds check_shape_done_holds p5c_res3_full_holds l2_res_nl3_holds l2_res_se3_holds p5v_cnt
        p5v_ncs p5v_wt p5v_pend p5v_ekc p5v_ekb p5v_old p5v_out p5v_chain gone_partial_reply_holds p5_contracts).
    + exact (pass6_holds check_bounded_holds RI3_reply RI3_mono).
    + exact (pass7_holds_RI3 check_bounded_holds (strnlen_holds memchr_holds) memcpy_holds
        (check_shape_event_holds (next_line_holds memchr_holds) strlen_holds bcmp_holds check_shape_done_holds)
        (fun B API LS SH SK ra empty rc fx HF => proj2 (proj2 (frame_contracts B API LS SH SK ra empty rc fx HF)))).
    + exact (pass8_holds check_bounded_holds RI3_reply RI3_mono).
    + exact (pass9_holds check_bounded_holds pthread_mutex_lock_holds pthread_mutex_unlock_holds RI3_reply
        RI3_mono).
  - exact (exit_holds CS_reply RI3_reply pack3_form
      (fun B API LS SH SK ra empty rc fx HF => proj1 (exit_contracts B API LS SH SK ra empty rc fx HF))
      (fun B API LS SH SK ra empty rc fx HF => proj1 (proj2 (exit_contracts B API LS SH SK ra empty rc fx HF)))
      (fun B API LS SH SK ra empty rc fx HF => proj2 (proj2 (exit_contracts B API LS SH SK ra empty rc fx HF)))
      check_shape_done_holds exit_res_fin_reply_d exit_res_ends_reply_s exit_res_reset_reply_s RI3_end_ok).
Qed.

Theorem ubsan_halts_of_parts : Statements.ubsan_halts.
Proof. exact (ubsan_halts_of_frame_p3 CS_reply CS_reply_ok frame_ubsan_holds fuzz_reply_slot_parts). Qed.

