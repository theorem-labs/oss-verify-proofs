(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the harness walk of LLVMFuzzerTestOneInput on the UBSan image with every callee
   contract discharged by its walk, in the shape of libreac/fuzz_decode's released
   lib/U/Prog/LLVMFuzzerTestOneInput_link.v. The allocator contracts come from the frame (frame_allocator); memcpy,
   memset and bcmp are the kit's walks; spec_msg_step, the diginet_* functions and the check_* functions are this
   unit's walks (diginet_cursor_init, diginet_msg_next and diginet_body_check relocated from fuzz_frame, whose code is
   byte-identical in this image). The unit links no calloc. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import
memcpy memset spec_msg_step diginet_cursor_init diginet_msg_next diginet_body_check diginet_personality_of
diginet_meter_segments diginet_decoder_init diginet_decoder_next check_cursor_step check_cursor_message
check_events_step check_events_fields check_refusal
LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_owed LLVMFuzzerTestOneInput.
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
  assert (MALLOC : forall fx' : YK11.FPState, @malloc_contract fx' rc B API) by (intros fx'; exact (proj1 (FA fx'))).
  assert (FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API)
    by (intros fx'; exact (proj1 (proj2 (FA fx')))).
  pose proof memcpy_holds as MC. pose proof memset_holds as MS.
  pose proof spec_msg_step_holds as SMS.
  pose proof diginet_cursor_init_holds as CI. pose proof diginet_msg_next_holds as MN.
  pose proof (diginet_body_check_holds CI MN) as BC.
  pose proof diginet_personality_of_holds as PO.
  pose proof diginet_decoder_init_holds as DI. pose proof diginet_decoder_next_holds as DN.
  pose proof check_cursor_step_holds as CCS. pose proof check_cursor_message_holds as CCM.
  pose proof check_events_step_holds as CES. pose proof check_events_fields_holds as CEF.
  pose proof (check_refusal_holds BC) as CR.
  exact (LLVMFuzzerTestOneInput_holds_of B API MALLOC FREE ERRNO_LOW SINK (owed_evt SMS MS MC) MC MS SMS CI MN PO DI
           DN CCS CCM CES CEF CR).
Qed.

End L.
