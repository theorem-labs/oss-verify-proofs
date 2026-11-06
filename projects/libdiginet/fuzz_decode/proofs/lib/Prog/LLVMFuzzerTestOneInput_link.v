(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the per-callee bundle, as libreac/fuzz_decode's released
   lib/Prog/LLVMFuzzerTestOneInput_link.v. It takes the frame allocator apart and hands the harness walk every
   contract it assumes: malloc and free from the allocator, memset and memcpy from the kit's walks, the library's
   diginet_cursor_init, diginet_msg_next, diginet_personality_of, diginet_decoder_init, diginet_decoder_next
   (with diginet_meter_segments) and diginet_body_check, the harness's five check_ functions (check_events_fields
   with bcmp), and the segment walks of LLVMFuzzerTestOneInput_seg.v / _seg2.v. The unit links no calloc. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import
  memset_c memcpy_c bcmp_c diginet_cursor_init_c diginet_msg_next_c diginet_personality_of_c
  diginet_meter_segments_c diginet_decoder_init_c diginet_decoder_next_c diginet_body_check_c
  check_cursor_step_c check_cursor_message_c check_events_step_c check_events_fields_c check_refusal_c
  LLVMFuzzerTestOneInput_seg LLVMFuzzerTestOneInput_seg2.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import
  memset memcpy bcmp diginet_cursor_init diginet_msg_next diginet_personality_of diginet_meter_segments
  diginet_decoder_init diginet_decoder_next diginet_body_check
  check_cursor_step check_cursor_message check_events_step check_events_fields check_refusal
  LLVMFuzzerTestOneInput_cstep LLVMFuzzerTestOneInput_dstep LLVMFuzzerTestOneInput_dsysex
  LLVMFuzzerTestOneInput_dchan LLVMFuzzerTestOneInput_setup LLVMFuzzerTestOneInput_cloop
  LLVMFuzzerTestOneInput_dloop
  LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput.
Import ListNotations.
Local Open Scope Z_scope.

Section L.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis SINK : lf_sink_env B.

Theorem LLVMFuzzerTestOneInput_holds : LLVMFuzzerTestOneInput_sr_contract B API.
Proof.
  intros BI.
  assert (MALLOC : forall fx' : YK11.FPState, @malloc_contract fx' rc B API) by (intros fx'; exact (proj1 (FA fx'))).
  assert (FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API)
    by (intros fx'; exact (proj1 (proj2 (FA fx')))).
  destruct (FA fx) as (_ & _ & _ & _ & _ & _ & _ & _ & BND & _).
  pose proof memset_holds as MSET. pose proof memcpy_holds as MCPY. pose proof bcmp_holds as BCMP.
  pose proof diginet_cursor_init_holds as CIN. pose proof diginet_msg_next_holds as MNX.
  pose proof diginet_personality_of_holds as POF. pose proof diginet_meter_segments_holds as MSG.
  assert (DIN : diginet_decoder_init_contract) by (eapply diginet_decoder_init_holds; eassumption).
  assert (DNX : diginet_decoder_next_contract) by (eapply diginet_decoder_next_holds; eassumption).
  assert (DBC : diginet_body_check_contract) by (eapply diginet_body_check_holds; eassumption).
  pose proof check_cursor_step_holds as CCS. pose proof check_cursor_message_holds as CCM.
  pose proof check_events_step_holds as CES.
  assert (CEF : check_events_fields_contract) by (eapply check_events_fields_holds; eassumption).
  assert (CRF : check_refusal_contract) by (eapply check_refusal_holds; eassumption).
  exact (LLVMFuzzerTestOneInput_holds_of B API MALLOC FREE ERRNO_LOW SINK BND MSET MCPY CIN MNX POF DIN DNX
    CCS CCM CES CEF CRF cstep_holds dstep_holds dsysex_holds dchan_holds setup_holds cloop_holds dsetup_holds
    dloop_holds BI).
Qed.

End L.
