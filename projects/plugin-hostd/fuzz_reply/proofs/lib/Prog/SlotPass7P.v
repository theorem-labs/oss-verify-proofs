From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract ContractT FrameAPI SlotKept SlotPack
  AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import Statement StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import relay_event_c check_bounded_c SlotInv
  SlotSteps SlotRes KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import relay_event_b_c check_shape_event_c
  strnlen_c memcpy_c SlotPass7RV SlotPass7D SlotPass7R SlotPass7S SlotPass7T1 SlotPass7T2 SlotPass7T3 SlotPass7S1
  SlotPass7S2b SlotPass7S3 SlotRI3 SlotPass7Res.
Import ListNotations.
Local Open Scope Z_scope.

Theorem pass7_holds : forall (F : ResFormT) RI,
  RI_mono RI -> op7_res_s F RI ->
  check_bounded_contract -> strnlen_contract -> memcpy_contract -> check_shape_event_contract ->
  (forall B API LS SH SK ra empty rc fx, frame_facts B API LS SH SK ra empty ->
     @malloc_contract_rt fx rc B (API rc) F /\ @free_contract_rt fx rc B (API rc) F /\
     @relay_event_contract fx rc B (API rc) F) ->
  pass_ok RI 7.
Proof.
  intros F RI RIM HR CB SN MC CK HCT.
  apply (pass7_of F RI); [| |exact RIM|exact CB|exact HCT].
  - exact (op7_chain_of F RI SN MC CK HR (op7_c1_holds F RI) (op7_c2_holds F RI) (op7_c3_holds F RI)).
  - exact (op7_rebuild_of RI op7_rb_image_holds op7_rb_stack_holds op7_rb_globals_holds op7_rb_output_holds
      op7_rb_driver_holds op7_rb_relay_holds op7_rb_move_holds).
Qed.

Theorem pass7_holds_RI3 : check_bounded_contract -> strnlen_contract -> memcpy_contract ->
  check_shape_event_contract -> (forall B API LS SH SK ra empty rc fx, frame_facts B API LS SH SK ra empty ->
  @malloc_contract_rt fx rc B (API rc) pack3_form /\ @free_contract_rt fx rc B (API rc) pack3_form /\
  @relay_event_contract fx rc B (API rc) pack3_form) -> pass_ok RI3_reply 7.
Proof.
  intros CB SN MC CK HCT.
  exact (pass7_holds pack3_form RI3_reply RI3_mono op7_res_s_RI3 CB SN MC CK HCT).
Qed.
