From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YM05 YL0i YH02 YI5b YI5c YL0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Contract Img0 FrameAPI SlotAgree AgreeLift
  ZAllocator FrameProof AllocCf AgreeZlib.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import snprintf LLVMFuzzerTestOneInput_c
  LLVMFuzzerTestOneInput_inv Statement LLVMFuzzerTestOneInput_cfb LLVMFuzzerTestOneInput_end_cg
  LLVMFuzzerTestOneInput_case0_cg LLVMFuzzerTestOneInput_case1_cg LLVMFuzzerTestOneInput_case2_cg
  LLVMFuzzerTestOneInput_case3_cg.
Import ListNotations.
Local Open Scope Z_scope.

Section T.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FR : llvm_frame rc B API SH SK.
Hypothesis MCF : forall fx' : YK11.FPState, @malloc_contract_cf fx' rc B API.
Hypothesis FCF : forall fx' : YK11.FPState, @free_contract_cf fx' rc B API.
Hypothesis LIM : llvm_limlaw B API.

Theorem llvm_cg_holds : LLVMFuzzerTestOneInput_contract_cg B API.
Proof.
  apply (llvm_contract_of_cases_cf B API FR MCF FCF LIM). intros BI.
  pose proof FR as (HA & Hel & _).
  pose proof (fun fx' => malloc_ag_of_cf B API LIM (MCF fx')) as HM.
  destruct (HA fx) as (_ & _ & _ & _ & _ & SLACK & _).
  intros op3 Hop.
  assert (E : op3 = 0 \/ op3 = 1 \/ op3 = 2 \/ op3 = 3) by lia.
  destruct E as [-> | [-> | [-> | ->]]].
  - apply llvm_case0_ok_cf; first [exact HM | exact FCF | exact Hel | exact SLACK | exact snprintf_holds].
  - apply llvm_case1_ok_cf.
  - apply llvm_case2_ok_cf.
  - apply llvm_case3_ok_cf; first [exact HM | exact FCF | exact Hel | exact SLACK | exact snprintf_holds].
Qed.

End T.

Theorem boxreg_slot_cg_frame : forall (LS : lib_shape),
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
  - unfold LLVM_K, LLVM_FRAME, SLOT_STACK. lia.
  - apply ret_ok_of_even. vm_compute. reflexivity.
Qed.
