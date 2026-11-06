(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs: ported from reac-repacer/fuzz_uci proofs/reac-repacer/fuzz_uci/lib/U/Prog/LLVMFuzzerTestOneInput_cgt.v
   at bc49657c087aa7d6ab0af1ffb2cb67fa08b15de1; module path, the name egress_slot_cg_frame, LLVM_K from check_inject, and
   Section L's callees those of this unit's lib/U/Prog/LLVMFuzzerTestOneInput_link.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_egress/lib/U/Prog/LLVMFuzzerTestOneInput_cgt.v, with its module paths and module names changed; 10 of its 51 lines of code are new or changed and 45 lines of the source are left out. *)
(* ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/U/Prog/LLVMFuzzerTestOneInput_cgt.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_frame; llvm_cg_holds takes the crash-free SR contract of LLVMFuzzerTestOneInput (U/Prog/Statement.v slot_sr_cf_all) as a hypothesis in place of decode's LLVMFuzzerTestOneInput_holds_cf, the walk of the harness; the image links no calloc, so there is no calloc hypothesis; decode_slot_cg_frame is frame_slot_cg_frame and takes slot_sr_cf_all as its first hypothesis; the stack bound is LLVMFuzzerTestOneInput_c.v llvm_K_slot; module path OSSVerify.Proofs.libdiginet.fuzz_frame.lib. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YH02 YI5b YI5c YL0s.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Contract Img0 FrameAPI SlotAgree AgreeLift ZAllocator
  FrameProof AllocCf AgreeZlib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c Statement
  LLVMFuzzerTestOneInput_cfb LLVMFuzzerTestOneInput_gcg.
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
Hypothesis SRCF : slot_sr_cf_all.

Theorem llvm_cg_holds : LLVMFuzzerTestOneInput_contract_cg B API.
Proof. apply llvm_g_of_sr_cf. exact (SRCF rc fx LS B API SH SK FR MCF FCF LIM). Qed.

End L.

Theorem frame_slot_cg_frame : slot_sr_cf_all -> forall (LS : lib_shape),
  (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) ->
  (forall b n, @lib_room LS b n -> llvm_room_cf b) ->
  (forall n b, @lib_delta LS n b = b) ->
  forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
    @lib_contract_cg fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
      llvm_G frame_RELRO llvm_GI j ENTRY RA_LIB EMPTY SLOT_STACK.
Proof.
  intros SRCF LS HK HR HD rc fx j Hj.
  apply (@llvm_cg_holds fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink).
  - unfold llvm_frame. split; [exact (zlib_frame_allocator rc)|]. split; [exact (errno_below_ceiling rc)|].
    repeat split; vm_compute; reflexivity.
  - intros fx'. exact (@zlib_malloc_contract_cf fx' rc).
  - intros fx'. exact (@zlib_free_contract_cf fx' rc).
  - exact (zlib_limit rc).
  - exact SRCF.
  - unfold llvm_binds. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    exact (@zlib_allocator_extra rc).
  - split; [intros pl fs K; rewrite HK; apply t_eq_refl|]. split; [exact HR | exact HD].
  - exact Hj.
  - exact llvm_K_slot.
  - apply ret_ok_of_even. vm_compute. reflexivity.
Qed.
