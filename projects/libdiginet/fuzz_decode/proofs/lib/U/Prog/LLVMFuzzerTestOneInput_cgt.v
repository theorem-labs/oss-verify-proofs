(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the UBSan image's cut-free slot contract, as libreac/fuzz_decode's released
   lib/U/Prog/LLVMFuzzerTestOneInput_cgt.v. Section L is the cf twin of lib/U/Prog/LLVMFuzzerTestOneInput_link.v:
   malloc at the agree room from the kit's malloc_contract_cf and the allocator's limit law (malloc_ag_of_cf), free
   from free_contract_cf, every other callee from its walk as the link takes it (evt contracts, no allocator).
   decode_slot_cg_frame instantiates it at the frame's allocator. The unit links no calloc, so decode's CCF
   hypothesis and calloc_ag_of_cf are gone. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YH02 YI5b YI5c YL0s.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import SlotAgree ZAllocator FrameProof AllocCf
  AgreeZlib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import Statement LLVMFuzzerTestOneInput_end
  LLVMFuzzerTestOneInput_cfb LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_gcg.
Import ListNotations.
Local Open Scope Z_scope.

Section L.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FR : llvm_frame rc B API SH SK.
Hypothesis MCF : forall fx' : YK11.FPState, @malloc_contract_cf fx' rc B API.
Hypothesis FCF : forall fx' : YK11.FPState, @free_contract_cf fx' rc B API.
Hypothesis LIM : llvm_limlaw B API.

Theorem LLVMFuzzerTestOneInput_holds_cf : LLVMFuzzerTestOneInput_sr_contract_cf B API.
Proof.
  intros BI.
  pose proof FR as (_ & ERRNO_LOW & _).
  pose proof (llvm_sink_env rc B API SH SK BI FR) as SINK.
  assert (MALLOC : forall fx' : YK11.FPState, @malloc_contract_ag fx' rc B API)
    by (intros fx'; exact (malloc_ag_of_cf B API LIM (MCF fx'))).
  pose proof memcpy_holds as MC. pose proof memset_holds as MS.
  pose proof spec_msg_step_holds as SMS.
  pose proof diginet_cursor_init_holds as CI. pose proof diginet_msg_next_holds as MN.
  pose proof (diginet_body_check_holds CI MN) as BC.
  pose proof diginet_personality_of_holds as PO.
  pose proof diginet_decoder_init_holds as DI. pose proof diginet_decoder_next_holds as DN.
  pose proof check_cursor_step_holds as CCS. pose proof check_cursor_message_holds as CCM.
  pose proof check_events_step_holds as CES. pose proof check_events_fields_holds as CEF.
  pose proof (check_refusal_holds BC) as CR.
  exact (LLVMFuzzerTestOneInput_holds_of_cf B API MALLOC FCF ERRNO_LOW SINK (owed_evt SMS MS MC) MC MS SMS CI MN PO
           DI DN CCS CCM CES CEF CR BI).
Qed.

Theorem llvm_cg_holds : LLVMFuzzerTestOneInput_contract_cg B API.
Proof. apply llvm_g_of_sr_cf. exact LLVMFuzzerTestOneInput_holds_cf. Qed.

End L.

Theorem decode_slot_cg_frame : forall (LS : lib_shape),
  (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) ->
  (forall b n, @lib_room LS b n -> llvm_room_cf b) ->
  (forall n b, @lib_delta LS n b = b) ->
  forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
    @lib_contract_cg fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
      llvm_G frame_RELRO llvm_GI j ENTRY RA_LIB EMPTY SLOT_STACK.
Proof.
  intros LS HK HR HD rc fx j Hj.
  apply (@llvm_cg_holds fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink).
  - unfold llvm_frame. split; [exact (zlib_frame_allocator rc)|]. split; [exact (errno_below_ceiling rc)|].
    repeat split; vm_compute; reflexivity.
  - intros fx'. exact (@zlib_malloc_contract_cf fx' rc).
  - intros fx'. exact (@zlib_free_contract_cf fx' rc).
  - exact (zlib_limit rc).
  - unfold llvm_binds. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    exact (@zlib_allocator_extra rc).
  - split; [intros pl fs K; rewrite HK; apply t_eq_refl|]. split; [exact HR | exact HD].
  - exact Hj.
  - unfold LLVM_K, LLVM_FRAME, ALLOC_STACK, SLOT_STACK. lia.
  - apply ret_ok_of_even. vm_compute. reflexivity.
Qed.
