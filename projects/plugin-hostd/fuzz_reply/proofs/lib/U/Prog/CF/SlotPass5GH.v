From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract ContractT FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import relay_instance_gone_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import strnlen_c memcpy_c memchr_c memmove_c strlen_c __errno_location_c pthread_mutex_lock_c pthread_mutex_unlock_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import list_push_c send_line_b_c gesture_end_b_c drain_b_c strndup_rt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import strrchr_c strcmp_c memrchr_c snprintf_c strncmp_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import list_drop_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import strnlen memcpy memchr memmove strlen __errno_location pthread_mutex_lock pthread_mutex_unlock.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import list_push send_line_b gesture_end_b drain_b.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import strrchr strcmp memrchr snprintf strncmp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import list_drop SlotPass5G relay_instance_gone_b.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import AllocPackGSF AllocPack3Ag.

Lemma gone_partial_of_rig :
  (forall (fx : YK11.FPState) (rc : YM05.RunCeil) (Bm : malloc_syms) (API : AllocAPI Bm),
     AllocExtra Bm (aa_MR API) -> ctx_owned Bm API -> block_slack_present Bm API -> ms_free Bm = 0x15f4c ->
     (forall L A mem md, aa_MR API L A mem md -> NoDup (map fst (blocks L A))) ->
     forall RF : ResFormT, pthread_mutex_lock_contract -> pthread_mutex_unlock_contract -> snprintf_contract ->
     strlen_contract -> strncmp_contract ->
     (forall fx' : YK11.FPState, @free_contract_rt fx' rc Bm API RF) ->
     (forall fx' : YK11.FPState, @drain_contract fx' rc Bm API RF) ->
     (forall fx' : YK11.FPState, @gesture_end_contract fx' rc Bm API RF) ->
     @relay_instance_gone_contract fx rc Bm API RF) ->
  forall B API LS SH SK ra empty rc, frame_facts B API LS SH SK ra empty -> gone_partial_S rc B (API rc).
Proof.
  intros RIG B API LS SH SK ra empty rc
    (SEG & RA2 & HMAL & HFREE & HREAL & HCAL & HERR & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 &
     F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27 & F28 & F29 & F30 & F31 & FA).
  pose proof (HERR rc) as ERR.
  pose proof (memmove_holds memcpy_holds) as MMV.
  assert (SLCS : forall fx' : YK11.FPState, @send_line_contract fx' rc B (API rc) pack3_ag_formT).
  { intro fx'.
    destruct (FA fx') as (MAL & FRE & FNC & REAL & CAL & SLK & CTX & LOW & NDP & BW & EU & GRW & AX & NG & NR).
    destruct (REAL 0x178f8 HREAL) as [RAC RNC].
    apply send_line_holds; first [assumption | exact memcpy_holds | exact __errno_location_holds]. }
  assert (FRS : forall fx' : YK11.FPState, @free_contract_rt fx' rc B (API rc) pack3_ag_formT)
    by (intro fx'; destruct (FA fx') as (_ & FRE & _); exact FRE).
  assert (DRN : forall fx' : YK11.FPState, @drain_contract fx' rc B (API rc) pack3_ag_formT).
  { intro fx'.
    destruct (FA fx') as (MAL & FRE & FNC & REAL & CAL & SLK & CTX & LOW & NDP & BW & EU & GRW & AX & NG & NR).
    destruct (REAL 0x178f8 HREAL) as [RAC RNC].
    assert (LPC : @list_push_contract fx' rc B (API rc) pack3_ag_formT)
      by (apply list_push_holds; first [assumption | exact memcpy_holds]).
    assert (LDC : @list_drop_contract fx' rc B (API rc) pack3_ag_formT) by (apply list_drop_holds; assumption).
    pose proof (strndup_holds_rt B (API rc) SEG HMAL ERR pack3_ag_formT MAL (strnlen_holds memchr_holds) memcpy_holds)
      as SDC.
    exact (drain_holds B (API rc) pack3_ag_formT AX CTX SLK BW EU HFREE NDP RAC RNC HMAL __errno_location_holds (SLCS fx') LPC
      SDC FRE memchr_holds MMV memcpy_holds (strrchr_holds strlen_holds memrchr_holds) strcmp_holds strncmp_holds
      strlen_holds LDC). }
  assert (GEN : forall fx' : YK11.FPState, @gesture_end_contract fx' rc B (API rc) pack3_ag_formT).
  { intro fx'.
    destruct (FA fx') as (MAL & FRE & FNC & REAL & CAL & SLK & CTX & LOW & NDP & BW & EU & GRW & AX & NG & NR).
    pose proof (SLCS fx') as SLC.
    apply gesture_end_holds; first [assumption | exact NDP | exact strlen_holds]. }
  apply gone_partial_of_contract.
  intro fx.
  destruct (FA fx) as (MAL & FRE & FNC & REAL & CAL & SLK & CTX & LOW & NDP & BW & EU & GRW & AX & NG & NR).
  apply RIG; first [assumption | exact NDP | exact HFREE | exact pthread_mutex_lock_holds |
    exact pthread_mutex_unlock_holds | exact snprintf_holds | exact strlen_holds | exact strncmp_holds].
Qed.

Lemma gone_partial_holds : forall B API LS SH SK ra empty rc, frame_facts B API LS SH SK ra empty ->
  gone_partial_S rc B (API rc).
Proof. exact (gone_partial_of_rig (@relay_instance_gone_holds)). Qed.
