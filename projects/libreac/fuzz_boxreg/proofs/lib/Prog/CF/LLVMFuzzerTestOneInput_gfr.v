From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05 YL0i YH02 YI5b YI5c YL0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import Contract Img0 FrameAPI ZAllocator FrameProof.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import AllocCf AgreeZlib.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import snprintf.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog.CF Require Import LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput Statement LLVMFuzzerTestOneInput_end LLVMFuzzerTestOneInput_case0 LLVMFuzzerTestOneInput_case1 LLVMFuzzerTestOneInput_case2 LLVMFuzzerTestOneInput_case3.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Theorem boxreg_slot_g_frame : forall (LS : lib_shape),
  (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) ->
  (forall b n, @lib_room LS b n -> llvm_room b) ->
  (forall n b, @lib_delta LS n b = b) ->
  forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
    @lib_contract_cg fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
      llvm_G frame_RELRO llvm_GI j ENTRY RA_LIB EMPTY SLOT_STACK.
Proof.
  intros LS HK HR HD rc fx j Hj.
  assert (FR : llvm_frame rc src0_msyms (@zlib_API rc) src0_sink_head src0_sink).
  { unfold llvm_frame.
    split; [exact (fun fx' => frame_allocator_of_cf (rc := rc) (fx := fx') src0_msyms (@zlib_API rc)
      (zlib_frame_allocator rc fx') (@zlib_malloc_contract_cf fx' rc) (@zlib_free_contract_cf fx' rc) (zlib_limit rc))|].
    split; [exact (errno_below_ceiling rc)|].
    repeat split; vm_compute; reflexivity. }
  apply (@llvm_contract_of_cases fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink FR).
  - intros BI.
    pose proof FR as (HA & Hel & _).
    pose proof (fun fx' => proj1 (HA fx')) as HM.
    pose proof (fun fx' => proj1 (proj2 (HA fx'))) as HF.
    destruct (HA fx) as (_ & _ & _ & _ & _ & SLACK & _).
    intros op3 Hop.
    assert (E : op3 = 0 \/ op3 = 1 \/ op3 = 2 \/ op3 = 3) by lia.
    destruct E as [-> | [-> | [-> | ->]]].
    + apply llvm_case0_ok; first [exact HM | exact HF | exact Hel | exact SLACK | exact snprintf_holds].
    + apply llvm_case1_ok.
    + apply llvm_case2_ok.
    + apply llvm_case3_ok; first [exact HM | exact HF | exact Hel | exact SLACK | exact snprintf_holds].
  - unfold llvm_binds. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    exact (@zlib_allocator_extra rc).
  - split; [intros pl fs K; rewrite HK; apply t_eq_refl|]. split; [exact HR | exact HD].
  - exact Hj.
  - unfold LLVM_K, LLVM_FRAME, SLOT_STACK. lia.
  - apply ret_ok_of_even. vm_compute. reflexivity.
Qed.
