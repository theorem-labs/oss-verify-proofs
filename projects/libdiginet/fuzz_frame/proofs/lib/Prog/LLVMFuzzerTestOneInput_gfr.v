(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs: ported from reac-repacer/fuzz_uci proofs/reac-repacer/fuzz_uci/lib/Prog/LLVMFuzzerTestOneInput_gfr.v at bc49657c087a; module path, the name egress_slot_g_frame, LLVM_K from check_inject. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_egress/lib/Prog/LLVMFuzzerTestOneInput_gfr.v, with its module paths changed; 5 of its 34 lines of code are new or changed and 5 lines of the source are left out. *)
(* ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_gfr.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_frame; decode_slot_g_frame is frame_slot_g_frame and takes the SR contract of LLVMFuzzerTestOneInput (Statement.v slot_sr_all) as its first hypothesis; the stack bound is LLVMFuzzerTestOneInput_c.v llvm_K_slot; module path OSSVerify.Proofs.libdiginet.fuzz_frame.lib. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Reusable Require Import YM05 YL0i YH02 YI5b YI5c YL0s.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Import Contract Img0 FrameAPI ZAllocator FrameProof.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog Require Import LLVMFuzzerTestOneInput_c
  Statement LLVMFuzzerTestOneInput_end.
Import ListNotations.
Local Open Scope Z_scope.

Theorem frame_slot_g_frame : slot_sr_all -> forall (LS : lib_shape),
  (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) ->
  (forall b n, @lib_room LS b n -> llvm_room b) ->
  (forall n b, @lib_delta LS n b = b) ->
  forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
    @lib_contract_g fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
      llvm_G frame_RELRO llvm_GI j ENTRY RA_LIB EMPTY SLOT_STACK.
Proof.
  intros SRA LS HK HR HD rc fx j Hj.
  assert (FR : llvm_frame rc src0_msyms (@zlib_API rc) src0_sink_head src0_sink).
  { unfold llvm_frame. split; [exact (zlib_frame_allocator rc)|]. split; [exact (errno_below_ceiling rc)|].
    repeat split; vm_compute; reflexivity. }
  apply (@llvm_contract fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink FR SRA).
  - unfold llvm_binds. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    exact (@zlib_allocator_extra rc).
  - split; [intros pl fs K; rewrite HK; apply t_eq_refl|]. split; [exact HR | exact HD].
  - exact Hj.
  - exact llvm_K_slot.
  - apply ret_ok_of_even. vm_compute. reflexivity.
Qed.
