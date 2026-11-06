From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract ContractT FrameAPI SlotKept
  AllocPack3 SlotPack3 FrameProof.
From OSSVerify.plugin_hostd.fuzz_reply Require Statements.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import StatementKept SlotInv SlotSteps SlotRes SlotLoop.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import SlotCaps3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotRI3 SlotEntryRun SlotEntry SlotPass0 SlotPass1 SlotPass1w SlotPass7P SlotPass9 SlotResReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import check_bounded_c check_shape_event_c check_shape_done_c next_line_c strnlen_c memcpy_c memchr_c memmove_c memset_c strlen_c bcmp_c __errno_location_c pthread_mutex_lock_c pthread_mutex_unlock_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import op_add_c source_reset_c list_free_c relay_add_b_c list_push_c send_line_b_c relay_event_b_c gesture_end_b_c gestures_end_b_c relay_finish_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import list_find_c has_prefix_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import check_shape_ends_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import check_bounded check_shape_event check_shape_done next_line strnlen memcpy memchr memmove memset strlen bcmp __errno_location pthread_mutex_lock pthread_mutex_unlock.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import op_add source_reset list_free relay_add_b list_push send_line_b relay_event_b gesture_end_b gestures_end_b relay_finish_b.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import list_find has_prefix.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import check_shape_ends.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotExitMove SlotExitFin SlotExitScan SlotExit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import drain_b_c strndup_rt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import strrchr_c strcmp_c memrchr_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import drain_b.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import strrchr strcmp memrchr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import relay_remove_b_c check_no_loss_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import check_no_loss_read_c memcpy_same_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import gesture_model_c list_drop_c relay_remove_b check_no_loss.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import check_no_loss_read memcpy_same.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import gesture_model list_drop SlotPass4 SlotPass2.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import snprintf_c snprintf strncmp_c strncmp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotP2Res3 SlotP4Res3 SlotP5Res3 SlotP5Res3Full SlotPass5V SlotPass5V2 SlotPass5G SlotPass5GH SlotPass5.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import AllocPackGSF AllocPack3Ag.

Lemma frame_contracts : forall B API LS SH SK ra empty rc fx, frame_facts B API LS SH SK ra empty ->
  @op_add_contract fx rc B (API rc) pack3_ag_formT /\ @list_push_contract fx rc B (API rc) pack3_ag_formT /\
  (@malloc_contract_rt fx rc B (API rc) pack3_ag_formT /\ @free_contract_rt fx rc B (API rc) pack3_ag_formT /\
   @relay_event_contract fx rc B (API rc) pack3_ag_formT).
Proof.
  intros B API LS SH SK ra empty rc fx
    (SEG & RA2 & HMAL & HFREE & HREAL & HCAL & HERR & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 &
     F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27 & F28 & F29 & F30 & FA).
  destruct (FA rc fx) as (MAL & FRE & FNC & REAL & CAL & SLK & CTX & LOW & NDP & BW & EU & GRW & AX & NG & NR).
  destruct (REAL 0x17010 HREAL) as [RAC RNC].
  pose proof (HERR rc) as ERR.
  pose proof (memmove_holds memcpy_holds) as MMV.
  assert (LFR : @list_free_contract fx rc B (API rc) pack3_ag_formT) by (apply list_free_holds; assumption).
  assert (SRS : @source_reset_contract fx rc B (API rc) pack3_ag_formT)
    by (apply source_reset_holds; first [assumption | exact memset_holds]).
  assert (RAD : @relay_add_contract fx rc B (API rc) pack3_ag_formT)
    by (apply relay_add_holds; first [assumption | exact pthread_mutex_lock_holds | exact pthread_mutex_unlock_holds |
                                      exact memset_holds]).
  assert (SLC : @send_line_contract fx rc B (API rc) pack3_ag_formT)
    by (apply send_line_holds; first [assumption | exact memcpy_holds | exact __errno_location_holds]).
  split; [apply op_add_holds; assumption|].
  split; [apply list_push_holds; first [assumption | exact memcpy_holds]|].
  split; [exact MAL|]. split; [exact FRE|].
  apply relay_event_holds; first [assumption | exact pthread_mutex_lock_holds | exact pthread_mutex_unlock_holds |
                                  exact strlen_holds].
Qed.

Lemma exit_contracts : forall B API LS SH SK ra empty rc fx, frame_facts B API LS SH SK ra empty ->
  @relay_finish_contract fx rc B (API rc) pack3_ag_formT /\ @check_shape_ends_contract fx rc B (API rc) pack3_ag_formT /\
  @source_reset_contract fx rc B (API rc) pack3_ag_formT.
Proof.
  intros B API LS SH SK ra empty rc fx
    (SEG & RA2 & HMAL & HFREE & HREAL & HCAL & HERR & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 &
     F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27 & F28 & F29 & F30 & FA).
  destruct (FA rc fx) as (MAL & FRE & FNC & REAL & CAL & SLK & CTX & LOW & NDP & BW & EU & GRW & AX & NG & NR).
  destruct (REAL 0x17010 HREAL) as [RAC RNC].
  pose proof (HERR rc) as ERR.
  pose proof (memmove_holds memcpy_holds) as MMV.
  assert (LFR : @list_free_contract fx rc B (API rc) pack3_ag_formT) by (apply list_free_holds; assumption).
  assert (SLC : @send_line_contract fx rc B (API rc) pack3_ag_formT)
    by (apply send_line_holds; first [assumption | exact memcpy_holds | exact __errno_location_holds]).
  assert (GEC : @gesture_end_contract fx rc B (API rc) pack3_ag_formT)
    by (apply gesture_end_holds; first [assumption | exact strlen_holds]).
  assert (GSC : @gestures_end_contract fx rc B (API rc) pack3_ag_formT) by (apply gestures_end_holds; assumption).
  split; [apply relay_finish_holds; first [assumption | exact pthread_mutex_lock_holds |
                                           exact pthread_mutex_unlock_holds]|].
  split; [apply check_shape_ends_holds; first [assumption | exact (next_line_holds memchr_holds) |
                                               exact (list_find_holds bcmp_holds) |
                                               exact (has_prefix_holds strlen_holds bcmp_holds)]|].
  apply source_reset_holds; first [assumption | exact memset_holds].
Qed.

Lemma drain_contracts : forall B API LS SH SK ra empty rc fx, frame_facts B API LS SH SK ra empty ->
  @drain_contract fx rc B (API rc) pack3_ag_formT.
Proof.
  intros B API LS SH SK ra empty rc fx
    (SEG & RA2 & HMAL & HFREE & HREAL & HCAL & HERR & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 &
     F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27 & F28 & F29 & F30 & FA).
  destruct (FA rc fx) as (MAL & FRE & FNC & REAL & CAL & SLK & CTX & LOW & NDP & BW & EU & GRW & AX & NG & NR).
  destruct (REAL 0x17010 HREAL) as [RAC RNC].
  pose proof (HERR rc) as ERR.
  pose proof (memmove_holds memcpy_holds) as MMV.
  assert (SLC : @send_line_contract fx rc B (API rc) pack3_ag_formT)
    by (apply send_line_holds; first [assumption | exact memcpy_holds | exact __errno_location_holds]).
  assert (LPC : @list_push_contract fx rc B (API rc) pack3_ag_formT)
    by (apply list_push_holds; first [assumption | exact memcpy_holds]).
  pose proof (strndup_holds_rt B (API rc) SEG HMAL ERR pack3_ag_formT MAL (strnlen_holds memchr_holds) memcpy_holds)
    as SDC.
  exact (drain_holds B (API rc) pack3_ag_formT AX CTX SLK BW EU HFREE NDP RAC RNC HMAL __errno_location_holds SLC LPC SDC FRE
    memchr_holds MMV memcpy_holds (strrchr_holds strlen_holds memrchr_holds) strcmp_holds strncmp_holds strlen_holds).
Qed.

Lemma p4_contracts : forall B API LS SH SK ra empty rc fx, frame_facts B API LS SH SK ra empty ->
  @relay_remove_contract fx rc B (API rc) pack3_ag_formT /\ @check_no_loss_contract fx rc B (API rc) pack3_ag_formT /\
  @check_shape_ends_contract fx rc B (API rc) pack3_ag_formT /\ @source_reset_contract fx rc B (API rc) pack3_ag_formT.
Proof.
  intros B API LS SH SK ra empty rc fx HF.
  pose proof (drain_contracts B API LS SH SK ra empty rc fx HF) as DRC.
  destruct (exit_contracts B API LS SH SK ra empty rc fx HF) as (_ & CSE & SRS).
  destruct HF as (SEG & RA2 & HMAL & HFREE & HREAL & HCAL & HERR & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 &
    F17 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27 & F28 & F29 & F30 & FA).
  destruct (FA rc fx) as (MAL & FRE & FNC & REAL & CAL & SLK & CTX & LOW & NDP & BW & EU & GRW & AX & NG & NR).
  destruct (REAL 0x17010 HREAL) as [RAC RNC].
  pose proof (HERR rc) as ERR.
  pose proof (memmove_holds memcpy_holds) as MMV.
  assert (SLC : @send_line_contract fx rc B (API rc) pack3_ag_formT)
    by (apply send_line_holds; first [assumption | exact memcpy_holds | exact __errno_location_holds]).
  assert (GEC : @gesture_end_contract fx rc B (API rc) pack3_ag_formT)
    by (apply gesture_end_holds; first [assumption | exact strlen_holds]).
  assert (GSC : @gestures_end_contract fx rc B (API rc) pack3_ag_formT) by (apply gestures_end_holds; assumption).
  assert (LPC : @list_push_contract fx rc B (API rc) pack3_ag_formT)
    by (apply list_push_holds; first [assumption | exact memcpy_holds]).
  assert (LDC : @list_drop_contract fx rc B (API rc) pack3_ag_formT) by (apply list_drop_holds; assumption).
  assert (GMC : @gesture_model_contract fx rc B (API rc) pack3_ag_formT)
    by (apply gesture_model_holds; first [assumption | exact bcmp_holds | exact (list_find_holds bcmp_holds)]).
  split; [apply relay_remove_holds; first [assumption | exact memcpy_holds | exact memcpy_same_holds |
                                           exact pthread_mutex_lock_holds | exact pthread_mutex_unlock_holds]|].
  split; [apply check_no_loss_holds; first [assumption | exact (next_line_holds memchr_holds) | exact bcmp_holds]|].
  split; [exact CSE|exact SRS].
Qed.

Lemma p5_contracts : forall B API LS SH SK ra empty rc fx, frame_facts B API LS SH SK ra empty ->
  @check_no_loss_contract fx rc B (API rc) pack3_ag_formT /\ @check_shape_ends_contract fx rc B (API rc) pack3_ag_formT.
Proof.
  intros B API LS SH SK ra empty rc fx HF.
  destruct (p4_contracts B API LS SH SK ra empty rc fx HF) as (_ & CNL & CSE & _).
  split; assumption.
Qed.
