(* fuzz_lock's slot contract of LLVMFuzzerTestOneInput (FrameRet.v lib_contract_gr with the return lock_ret) at the
   image's own allocator and sink (src0_msyms, zlib_API, src0_sink_head, src0_sink), in the form of
   libreac/fuzz_decode's lib/Prog/LLVMFuzzerTestOneInput_gfr.v (release 25e3d17bdb50). Written by Theorem Labs.
   *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YM05 YL0i YH02 YI5b YI5c YL0s.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require Import Contract Img0 FrameAPI ZAllocator FrameProof
  SlotTopG.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog Require Import strlen_c check_lookup_c FrameRet
  LLVMFuzzerTestOneInput_c Statement LLVMFuzzerTestOneInput_end.
Import ListNotations.
Local Open Scope Z_scope.

Theorem lock_slot_g_frame : strlen_contract -> forall (LS : lib_shape),
  (forall pl fs K, @LIBK LS pl fs K = K (LL (lock_ret pl) fs [])) ->
  (forall b n, @lib_room LS b n -> llvm_room b) ->
  (forall n b, @lib_delta LS n b = b) ->
  forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
    @lib_contract_gr fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
      lock_ret llvm_G frame_RELRO llvm_GI j ENTRY RA_LIB EMPTY SLOT_STACK.
Proof.
  intros STRLEN LS HK HR HD rc fx j Hj.
  assert (FR : llvm_frame rc src0_msyms (@zlib_API rc) src0_sink_head src0_sink).
  { unfold llvm_frame. split; [exact (zlib_frame_allocator rc)|]. split; [exact (errno_below_ceiling rc)|].
    apply lock_sink_env; first [exact ms_segs_rsegs | reflexivity]. }
  apply (@llvm_contract fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink FR STRLEN).
  - unfold llvm_binds. split; [exact ms_segs_rsegs|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    exact (@zlib_allocator_extra rc).
  - split; [intros pl fs K; rewrite HK; apply t_eq_refl|]. split; [exact HR | exact HD].
  - exact Hj.
  - unfold LLVM_K, LLVM_FRAME, CL_STACK, CL_FRAME, ALLOC_STACK, SLOT_STACK. lia.
  - apply ret_ok_of_even. vm_compute. reflexivity.
Qed.
