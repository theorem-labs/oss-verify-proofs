(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs: ported from reac-repacer/fuzz_uci proofs/reac-repacer/fuzz_uci/lib/Prog/LLVMFuzzerTestOneInput_gfr.v at bc49657c087a; module path, the name egress_slot_g_frame, LLVM_K from check_inject. *)
(* The plain image's slot contract for any lib_shape whose continuation, room and delta are kept_shape's, as
   libreac/fuzz_decode's released lib/Prog/LLVMFuzzerTestOneInput_gfr.v (decode_slot_g_frame), over this unit's
   llvm_contract (LLVMFuzzerTestOneInput_end.v). fuzz_egress links no calloc and its deepest callee stack is
   CHECK_INJECT_STACK, so decode's CRT_STACK / CRT_FRAME / CALLOC_STACK are gone from the bound. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Reusable Require Import YM05 YL0i YH02 YI5b YI5c YL0s.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require Import Contract Img0 FrameAPI ZAllocator FrameProof.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Prog Require Import check_inject_c LLVMFuzzerTestOneInput_c
  Statement LLVMFuzzerTestOneInput_end.
Import ListNotations.
Local Open Scope Z_scope.

Theorem egress_slot_g_frame : forall (LS : lib_shape),
  (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) ->
  (forall b n, @lib_room LS b n -> llvm_room b) ->
  (forall n b, @lib_delta LS n b = b) ->
  forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
    @lib_contract_g fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
      llvm_G frame_RELRO llvm_GI j ENTRY RA_LIB EMPTY SLOT_STACK.
Proof.
  intros LS HK HR HD rc fx j Hj.
  assert (FR : llvm_frame rc src0_msyms (@zlib_API rc) src0_sink_head src0_sink).
  { unfold llvm_frame. split; [exact (zlib_frame_allocator rc)|]. split; [exact (errno_below_ceiling rc)|].
    repeat split; vm_compute; reflexivity. }
  apply (@llvm_contract fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink FR).
  - unfold llvm_binds. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    exact (@zlib_allocator_extra rc).
  - split; [intros pl fs K; rewrite HK; apply t_eq_refl|]. split; [exact HR | exact HD].
  - exact Hj.
  - unfold LLVM_K, LLVM_FRAME, CHECK_INJECT_STACK, CHECK_INJECT_FRAME, ALLOC_STACK, SLOT_STACK. lia.
  - apply ret_ok_of_even. vm_compute. reflexivity.
Qed.
