From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import
  YK11 YM05 YO0d YH02 YN33.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable.Q Require Import YW02 YT00 YT02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import ZAllocator Contract AllocCut AllocForm AllocPackCut.
Open Scope Z_scope.
Section R. Context {fx : FPState} {rc : RunCeil}.
Lemma zlib_realloc : forall pc, ms_realloc src0_msyms = Some pc ->
  realloc_contract src0_msyms (@zlib_API rc) pc /\ realloc_null_contract src0_msyms (@zlib_API rc) pc.
Proof using.
  intros pc Hpc. pose proof (@zlib_allocator_extra rc) as AX.
  assert (HB : ro_apart_b src0_msyms = true) by (vm_compute; reflexivity).
  split.
  - exact (realloc_contract_form src0_msyms (@zlib_API rc) sb_form sb_laws AX HB
      (@src0_realloc_realizes fx rc) realloc_safe_p_ok pc Hpc).
  - exact (realloc_null_contract_form src0_msyms (@zlib_API rc) sb_form sb_laws AX HB
      (@src0_realloc_null_realizes fx rc) pc Hpc).
Qed.
Lemma zlib_realloc_pack : forall pc, ms_realloc src0_msyms = Some pc ->
  realloc_contract_r src0_msyms (@zlib_API rc) pack_form pc /\
  realloc_null_contract_r src0_msyms (@zlib_API rc) pack_form pc.
Proof using.
  intros pc Hpc. pose proof (@zlib_allocator_extra rc) as AX.
  assert (HB : ro_apart_b src0_msyms = true) by (vm_compute; reflexivity).
  split.
  - exact (pack_realloc_contract src0_msyms (@zlib_API rc) AX HB
      (@src0_realloc_realizes fx rc) realloc_safe_p_ok pc Hpc).
  - exact (pack_realloc_null_contract src0_msyms (@zlib_API rc) AX HB
      (@src0_realloc_null_realizes fx rc) pc Hpc).
Qed.
End R.
