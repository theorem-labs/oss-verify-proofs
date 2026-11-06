(* fuzz_lock.ubsan's slot contract of LLVMFuzzerTestOneInput in crash-free form (AgreeRet.v lib_contract_cgr
   with the return lock_ret) at the image's own allocator and sink (src0_msyms, zlib_API, src0_sink_head,
   src0_sink), in the form of libreac/fuzz_decode's lib/U/Prog/LLVMFuzzerTestOneInput_cgt.v (release
   25e3d17bdb50), and the twin of the plain lib/Prog/LLVMFuzzerTestOneInput_gfr.v. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YM05 YL0i YH02 YI5b YI5c YL0s.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Contract Img0 FrameAPI ZAllocator
  SlotAgree AgreeLift FrameProof.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import FrameRet AgreeRet check_no_overread_c check_lookup_c check_no_overread_ccf check_lookup_ccf lt_cf_c
  LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_cf LLVMFuzzerTestOneInput_cg
  LLVMFuzzerTestOneInput_end Statement.
Import ListNotations.
Local Open Scope Z_scope.

Theorem lock_slot_cg_frame :
  (forall (rc : RunCeil) (fx : FPState), @check_no_overread_contract_cf fx rc src0_msyms (@zlib_API rc)) ->
  (forall (rc : RunCeil) (fx : FPState), @check_lookup_contract_cf fx rc src0_msyms (@zlib_API rc)) ->
  forall (LS : lib_shape),
  (forall pl fs K, @LIBK LS pl fs K = K (LL (lock_ret pl) fs [])) ->
  (forall b n, @lib_room LS b n -> llvm_room_cf b) ->
  (forall n b, @lib_delta LS n b = b) ->
  forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
    @lib_contract_cgr fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
      lock_ret llvm_G frame_RELRO llvm_GI j ENTRY RA_LIB EMPTY SLOT_STACK.
Proof.
  intros CNO CL LS HK HR HD rc fx j Hj.
  assert (BI : llvm_binds src0_msyms (@zlib_API rc)).
  { unfold llvm_binds. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    exact (@zlib_allocator_extra rc). }
  assert (FR : @llvm_frame rc src0_msyms (@zlib_API rc) src0_sink_head src0_sink).
  { unfold llvm_frame. split; [intros fx'; exact (zlib_frame_allocator rc fx')|].
    split; [exact (errno_below_ceiling rc)|]. repeat split; reflexivity. }
  apply llvm_cg_of_sr.
  - apply LLVMFuzzerTestOneInput_holds_cf.
    + exact (proj1 (proj2 FR)).
    + exact (llvm_sink_env rc src0_msyms (@zlib_API rc) src0_sink_head src0_sink BI FR).
    + intros fx'. exact (CNO rc fx').
    + intros fx'. exact (CL rc fx').
  - exact BI.
  - split; [intros pl fs K'; rewrite HK; apply t_eq_refl|]. split; [exact HR | exact HD].
  - exact Hj.
  - unfold LLVM_K, LLVM_FRAME, CL_STACK, CL_FRAME, ALLOC_STACK, SLOT_STACK. lia.
  - apply ret_ok_of_even. vm_compute. reflexivity.
Qed.
