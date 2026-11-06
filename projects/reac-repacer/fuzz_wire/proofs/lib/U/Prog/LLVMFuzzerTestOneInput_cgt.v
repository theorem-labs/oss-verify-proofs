(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for reac-repacer/fuzz_wire: the UBSan image's cut-free slot contract, as libreac/fuzz_decode's released
   lib/U/Prog/LLVMFuzzerTestOneInput_cgt.v (25e3d17bdb5) and reac-repacer/fuzz_uci's (ddb6d58bbed). Section L is the
   cf twin of lib/U/Prog/LLVMFuzzerTestOneInput_link.v: malloc at the agree room from the kit's malloc_contract_cf and
   the allocator's limit law (malloc_ag_of_cf), free from free_contract_cf, check_copy from its cf walk
   (check_copy_cg.v), memcpy and the seven checks with their rp_* callees from their walks as they are (evt contracts,
   no allocator). wire_slot_cg_frame (decode's decode_slot_cg_frame) instantiates it at the frame's allocator.
   The UBSan image has no symbol named `calloc` (musl's __libc_calloc is linked), so decode's CCF hypothesis and calloc_ag_of_cf are gone. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Prog Require Import
memcpy memmove bcmp reac_frame_clean_len reac_frame_is_reac is_tagged_reac rp_fwd_class rp_ret_accept rp_ds_accept
rp_meter_counter rp_counter rp_frame_channels rp_slot_width rp_slot_read rp_copy_untag
check_forward_c check_forward check_ret_c check_ret check_downstream_c check_downstream check_meter_c check_meter
check_counter_c check_counter check_width_c check_width check_read_c check_read check_copy_c cc_segs
LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Reusable Require Import YH02 YI5b YI5c YL0s.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require Import SlotAgree ZAllocator FrameProof AllocCf
  AgreeZlib.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Prog Require Import Statement LLVMFuzzerTestOneInput_end
  LLVMFuzzerTestOneInput_cfb check_copy_ccf check_copy_cg LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_gcg.
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
  enough (H : llvm_binds B API -> LLVMFuzzerTestOneInput_sr_contract_cf B API) by (intros BI; exact (H BI BI)).
  intros BI. pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  pose proof FR as (FA & ERRNO_LOW & _).
  pose proof (llvm_sink_env rc B API SH SK BI FR) as SINK.
  assert (MALPC : ms_malloc B = CC_MALLOC) by exact HMAL.
  assert (FREEPC : ms_free B = CC_FREE) by exact HFRE.
  assert (MALLOC : forall fx' : YK11.FPState, @malloc_contract_ag fx' rc B API)
    by (intros fx'; exact (malloc_ag_of_cf B API LIM (MCF fx'))).
  pose proof FCF as FREE.
  destruct (FA fx) as (_ & _ & _ & _ & _ & _ & CT & _ & BND & _).
  pose proof memcpy_holds as MC. pose proof bcmp_holds as BCMP.
  pose proof (check_forward_holds rp_fwd_class_holds) as CF.
  pose proof (check_ret_holds rp_ret_accept_holds) as CR.
  pose proof (check_downstream_holds (rp_ds_accept_holds is_tagged_reac_holds)) as CD.
  pose proof (check_meter_holds rp_meter_counter_holds) as CM.
  pose proof (check_counter_holds rp_counter_holds) as CN.
  pose proof (rp_frame_channels_holds reac_frame_clean_len_holds) as FCH.
  pose proof (check_width_holds FCH) as CW.
  pose proof (check_read_holds (rp_slot_read_holds (rp_slot_width_holds FCH))) as CRD.
  pose proof (rp_copy_untag_holds is_tagged_reac_holds (memmove_holds memcpy_holds) reac_frame_is_reac_holds) as CU.
  assert (CC : forall fx' : YK11.FPState, @check_copy_contract_cf fx' rc B API).
  { intros fx'. eapply (check_copy_holds_cf (fx := fx')); eassumption. }
  (* the cf walk's Section hypotheses, in order: MALLOC FREE ERRNO_LOW SINK BND CT MC CF CR CD CM CN CW CRD CC *)
  eapply LLVMFuzzerTestOneInput_holds_of_cf; eassumption.
Qed.

Theorem llvm_cg_holds : LLVMFuzzerTestOneInput_contract_cg B API.
Proof. apply llvm_g_of_sr_cf. exact LLVMFuzzerTestOneInput_holds_cf. Qed.

End L.

Theorem wire_slot_cg_frame : forall (LS : lib_shape),
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
  - unfold LLVM_K, LLVM_FRAME, CC_STACK, CHECK_COPY_FRAME, ALLOC_STACK, SLOT_STACK. lia.
  - apply ret_ok_of_even. vm_compute. reflexivity.
Qed.
