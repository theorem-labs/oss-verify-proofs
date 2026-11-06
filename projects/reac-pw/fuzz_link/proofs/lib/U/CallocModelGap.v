From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Reusable Require Import YO0i YO0f YO0d YM05 YH02.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U Require Import Contract FrameAPI ZAllocator FrameProof CallocSite.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require LLVMFuzzerTestOneInput_c.
Local Open Scope Z_scope.

(* lib/U/Prog/LLVMFuzzerTestOneInput_c.v names `llvm_calloc_model` (calloc_contract for calloc(1, 8856) at
   0x13be0) as a premise of the UBSan slot contract, because the frame's calloc contracts asked m * n < 4096.
   They now ask m * n < 2 ^ 62 (lib/U/Contract.v:153), and the premise follows from the frame's calloc_contract
   (lib/U/CallocSite.v calloc_model_site), from the allocator record frame_ubsan gives, and at link's own
   allocator zlib_API. *)

Section S.
Context {rc : RunCeil} {fx : FPState}.

Lemma llvm_calloc_model_of_contract : forall (B : malloc_syms) (API : AllocAPI B),
  calloc_contract B API LLVMFuzzerTestOneInput_c.LLVM_CALLOC ->
  ms_calloc B = Some LLVMFuzzerTestOneInput_c.LLVM_CALLOC ->
  LLVMFuzzerTestOneInput_c.llvm_calloc_model B API.
Proof.
  intros B API HCAL HC L A regs mem md b PRE RO H10 H11 HR HRm.
  exact (calloc_model_site B API HCAL HC L A regs mem md b PRE RO H10 H11 HR HRm).
Qed.

Lemma llvm_calloc_model_frame : forall (B : malloc_syms) (API : AllocAPI B),
  frame_allocator B API -> ms_calloc B = Some LLVMFuzzerTestOneInput_c.LLVM_CALLOC ->
  LLVMFuzzerTestOneInput_c.llvm_calloc_model B API.
Proof.
  intros B API FA HC. destruct FA as (_ & _ & _ & _ & HCAL & _).
  exact (llvm_calloc_model_of_contract B API (HCAL _ HC) HC).
Qed.

Lemma zlib_llvm_calloc_model : LLVMFuzzerTestOneInput_c.llvm_calloc_model src0_msyms (@zlib_API rc).
Proof. exact (llvm_calloc_model_frame src0_msyms (@zlib_API rc) (zlib_frame_allocator rc fx) eq_refl). Qed.

End S.
