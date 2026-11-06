(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the walk of LLVMFuzzerTestOneInput on the UBSan image ([0x12cfc, 0x13464), frame
   0x1f0), put together from its parts, each proved in its own file over the cuts of
   lib/U/Prog/LLVMFuzzerTestOneInput_mid.v:
   - the early path, size = 0 or size >= 2^26 (LLVMFuzzerTestOneInput_early.v: llvm_early);
   - the front, 0x12cfc to 0x12df8, with the malloc and the memcpy of fuzz_dup and the inlined spec_read_frame
     (LLVMFuzzerTestOneInput_front.v: llvm_front_holds);
   - the cursor loop, 0x12df8 to 0x12e8c (LLVMFuzzerTestOneInput_cursor.v: llvm_cursor_evt);
   - the decoder loop, 0x12e8c to 0x13384 (LLVMFuzzerTestOneInput_decoder.v: llvm_decoder_evt), whose body's first
     half, the inlined owed_at 0x12f10-0x131cc, is the hypothesis owed_segment here (LLVMFuzzerTestOneInput_owed.v's
     owed_evt discharges it in LLVMFuzzerTestOneInput_link.v);
   - check_refusal, free and the return (LLVMFuzzerTestOneInput_top.v: llvm_exit_evt, llvm_sr_of_parts).
   This file joins the two loops at 0x12e8c and hands the four parts to llvm_sr_of_parts; the callee contracts are
   Section hypotheses, which the link discharges with the callees' walks. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import
memcpy_c memset_c spec_msg_step_c diginet_cursor_init_c diginet_msg_next_c diginet_personality_of_c
diginet_decoder_init_c diginet_decoder_next_c check_cursor_step_c check_cursor_message_c check_events_step_c
check_events_fields_c check_refusal_c
LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_mid LLVMFuzzerTestOneInput_glue
LLVMFuzzerTestOneInput_early LLVMFuzzerTestOneInput_front
LLVMFuzzerTestOneInput_cursor LLVMFuzzerTestOneInput_decoder LLVMFuzzerTestOneInput_top.
Import ListNotations.
Open Scope Z_scope.

(* 0x12df8 to 0x13384: the cursor loop and then the decoder loop; the inlined owed_at of the decoder loop's body is
   owed_segment, which LLVMFuzzerTestOneInput_link.v discharges with LLVMFuzzerTestOneInput_owed.v's owed_evt *)
Lemma llvm_loops_evt :
  owed_segment ->
  diginet_cursor_init_contract -> diginet_msg_next_contract -> spec_msg_step_contract -> memset_contract ->
  check_cursor_step_contract -> check_cursor_message_contract ->
  diginet_personality_of_contract -> diginet_decoder_init_contract -> diginet_decoder_next_contract ->
  check_events_step_contract -> check_events_fields_contract ->
  forall F fc gp tp sv Sp lo buf nn body bb m0 ms,
    mid_env sv Sp lo buf nn body bb ->
    mid_at F fc gp tp sv Sp lo buf body bb m0 LLVM_PC_BODY ms ->
    evt rsegs (mid_at F fc gp tp sv Sp lo buf body bb m0 LLVM_PC_DECODER_OUT) ms.
Proof.
  intros OWED CI MN SMS MS CCS CCM PO DI DN CES CEF F fc gp tp sv Sp lo buf nn body bb m0 ms HE HA.
  eapply evt_cut.
  - exact (llvm_cursor_evt CI MN SMS MS CCS CCM F fc gp tp sv Sp lo buf nn body bb m0 ms HE HA).
  - intros ms' HA'.
    exact (llvm_decoder_evt OWED PO DI DN MS CES CEF F fc gp tp sv Sp lo buf nn body bb m0 ms' HE HA').
Qed.

Section M.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis MALLOC : forall fx' : YK11.FPState, @malloc_contract fx' rc B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= YM05.alloc_ceiling.
Hypothesis SINK : lf_sink_env B.
Context (OWED : owed_segment) (MC : memcpy_contract) (MS : memset_contract) (SMS : spec_msg_step_contract)
  (CI : diginet_cursor_init_contract) (MN : diginet_msg_next_contract)
  (PO : diginet_personality_of_contract) (DI : diginet_decoder_init_contract)
  (DN : diginet_decoder_next_contract)
  (CCS : check_cursor_step_contract) (CCM : check_cursor_message_contract)
  (CES : check_events_step_contract) (CEF : check_events_fields_contract) (CR : check_refusal_contract).

Theorem LLVMFuzzerTestOneInput_holds_of : LLVMFuzzerTestOneInput_sr_contract B API.
Proof.
  apply (llvm_sr_of_parts B API FREE ERRNO_LOW SINK).
  - intros j stk empty L A regs mem md ra p n b.
    exact (llvm_early B API SINK j stk empty L A regs mem md ra p n b).
  - intros stk empty L0 A0 regs0 mem0 md0 ra p n pl b.
    exact (llvm_front_holds B API MALLOC ERRNO_LOW MC stk empty L0 A0 regs0 mem0 md0 ra p n pl b).
  - exact (llvm_loops_evt OWED CI MN SMS MS CCS CCM PO DI DN CES CEF).
  - exact CR.
Qed.

End M.
