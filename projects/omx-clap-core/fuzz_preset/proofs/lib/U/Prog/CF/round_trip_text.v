From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes strcmp_c strlen_c same_c memcpy_c fuzz_alloc_ran_out_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import PjWriteHyp round_trip_text_c tx_put_c tx_value_c parse_noting_c pj_free_c fuzz_free_c pj_write_c write_value_c put_c PjWriteAdapt RttBase RttEntry RttStgTx1 RttStgTxv RttStgNl RttStgCmp RttStgOom RttStgFf RttStgSame RttStgEnd.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Local Open Scope Z_scope.

(* round_trip_text of the #102 ubsan twin (0x15334), CF form: the contract from the walk's stage statements (RttBase.v)
   and the stage lemmas; the mirror of P6-u's U top (lib/U/Prog/round_trip_text.v, origin/cold/h-rw-ide-20-p102-P6-u
   ee95a2850612) with CF Requires and SRCF.  rtt_entry_holds proves the prologue and pj_write up to stg_tx1's pre; the
   other stages chain through their own NEXT premises: tx1 -> txv -> nl -> cmp -> {oom (ran out: a0 = 1) | ff -> same ->
   end (a0 = 0)}.  The Section hypotheses are the callees' contracts the stage lemmas step over: free (ms_free B =
   0x18250, free in the symtab of the #102 ubsan twin 27566683, = lib/U/FrameAPI.v frame_ubsan; round_trip_text calls
   it at 0x153c8, 0x153e8 and 0x15454), pj_write, tx_put, tx_value, strcmp, strlen, parse_noting (the read-back of
   #102, no pj_parse), fuzz_alloc_ran_out (the out_of_memory tests), fuzz_free, same, memcpy, pj_free.
   round_trip_text_of_stages(_w) keep the stage statements as premises; round_trip_text_holds(_w) discharge them with
   the stage lemmas. *)

Section T.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Variable kw : jv -> Z.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
Hypothesis KW : forall t, (depth t <= 32)%nat -> 0 <= kw t <= PJ_PARSE_K.
Hypothesis HFREE : ms_free B = 0x18250.
Hypothesis FREEF : forall fx' : YK11.FPState, @free_contract_r fx' rc B API F.
Hypothesis PJW : @pj_write_hyp fx rc B API F kw.
Hypothesis TXP : forall fx' : YK11.FPState, @tx_put_contract fx' rc B API F.
Hypothesis TXV : forall fx' : YK11.FPState, @tx_value_contract fx' rc B API F.
Hypothesis SC : strcmp_contract.
Hypothesis SL : strlen_contract.
Hypothesis SAME : same_contract.
Hypothesis MC : memcpy_contract.
Hypothesis PNC : forall fx' : YK11.FPState, @parse_noting_contract fx' rc B API F.
Hypothesis FRO : fuzz_alloc_ran_out_contract.
Hypothesis FF : forall fx' : YK11.FPState, @fuzz_free_contract fx' rc B API F.
Hypothesis PJF : forall fx' : YK11.FPState, @pj_free_contract fx' rc B API F.

Theorem round_trip_text_of_stages :
  stg_end_st B API F -> stg_same_st B API F -> stg_ff_st B API F -> stg_oom_st B API F -> stg_cmp_st B API F ->
  stg_nl_st B API F -> stg_txv_st B API F -> stg_tx1_st B API F ->
  round_trip_text_contract B API F.
Proof.
  intros E8 E7 E6 E5 E4 E3 E2 E1.
  eapply rtt_entry_holds; eassumption.
Qed.

Theorem round_trip_text_holds : round_trip_text_contract B API F.
Proof.
  assert (E8 : stg_end_st B API F) by (eapply stg_end_holds; eassumption).
  assert (E7 : stg_same_st B API F) by (eapply stg_same_holds; eassumption).
  assert (E6 : stg_ff_st B API F) by (eapply stg_ff_holds; eassumption).
  assert (E5 : stg_oom_st B API F) by (eapply stg_oom_holds; eassumption).
  assert (E4 : stg_cmp_st B API F) by (eapply stg_cmp_holds; eassumption).
  assert (E3 : stg_nl_st B API F) by (eapply stg_nl_holds; eassumption).
  assert (E2 : stg_txv_st B API F) by (eapply stg_txv_holds; eassumption).
  assert (E1 : stg_tx1_st B API F) by (eapply stg_tx1_holds; eassumption).
  exact (round_trip_text_of_stages E8 E7 E6 E5 E4 E3 E2 E1).
Qed.

End T.

Lemma rtt_pjw_k : forall t : jv, (depth t <= 32)%nat -> 0 <= PJW_K t <= PJ_PARSE_K.
Proof.
  intros t Hd. unfold PJW_K, WV_K.
  assert (H0 : 0 <= Z.of_nat (depth t) <= 32) by lia.
  assert (C : 0 <= WV_FR /\ PJW_FR + Z.max (WV_FR * 33 + WV_KMAX) (Z.max PUT_K ALLOC_STACK) <= PJ_PARSE_K /\
              0 <= PJW_FR /\ 0 <= WV_KMAX) by (vm_compute; repeat split; discriminate).
  destruct C as (C1 & C2 & C3 & C4).
  assert (M : WV_FR * (Z.of_nat (depth t) + 1) <= WV_FR * 33) by nia.
  split; lia.
Qed.

Section W.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
Hypothesis HFREE : ms_free B = 0x18250.
Hypothesis FREEF : forall fx' : YK11.FPState, @free_contract_r fx' rc B API F.
Hypothesis PJWC : forall fx' : YK11.FPState, @pj_write_contract fx' rc B API F.
Hypothesis TXP : forall fx' : YK11.FPState, @tx_put_contract fx' rc B API F.
Hypothesis TXV : forall fx' : YK11.FPState, @tx_value_contract fx' rc B API F.
Hypothesis SC : strcmp_contract.
Hypothesis SL : strlen_contract.
Hypothesis SAME : same_contract.
Hypothesis MC : memcpy_contract.
Hypothesis PNC : forall fx' : YK11.FPState, @parse_noting_contract fx' rc B API F.
Hypothesis FRO : fuzz_alloc_ran_out_contract.
Hypothesis FF : forall fx' : YK11.FPState, @fuzz_free_contract fx' rc B API F.
Hypothesis PJF : forall fx' : YK11.FPState, @pj_free_contract fx' rc B API F.

Theorem round_trip_text_of_stages_w :
  stg_end_st B API F -> stg_same_st B API F -> stg_ff_st B API F -> stg_oom_st B API F -> stg_cmp_st B API F ->
  stg_nl_st B API F -> stg_txv_st B API F -> stg_tx1_st B API F ->
  round_trip_text_contract B API F.
Proof.
  intros E8 E7 E6 E5 E4 E3 E2 E1.
  eapply (round_trip_text_of_stages B API F PJW_K); try eassumption.
  - exact rtt_pjw_k.
  - apply (pj_write_adapt B API F (rtt_AX B API HSEG FA) PJWC).
Qed.

Theorem round_trip_text_holds_w : round_trip_text_contract B API F.
Proof.
  eapply (round_trip_text_holds B API F PJW_K); try eassumption.
  - exact rtt_pjw_k.
  - apply (pj_write_adapt B API F (rtt_AX B API HSEG FA) PJWC).
Qed.

End W.
