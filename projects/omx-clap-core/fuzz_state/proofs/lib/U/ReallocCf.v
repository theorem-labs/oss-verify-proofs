From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0s YK0i YK15 YM06 YM06_cf YM05 YM02 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import
YO0i YO0f YO0g YO0q YO0x YO0d YO0e YO05 YO02 YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO16 YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO10 YO0s YO0u YO15 YN03 YN2b YN33.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0d_cf YO03_cf YO0n_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import AllocSI AllocGS AllocFree AllocMalloc AllocRealloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import AllocMB AllocMallocPath AllocFreePath AllocReallocOK.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract AllocSlots AllocCut AllocForm SlotAgree AllocCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import AllocPack AllocPackRoom AllocPackCut.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import AllocPackGSF AllocPackGSFm AllocPackGSFr AllocPackCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import AllocReallocRoom AllocUnif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YH02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import AllocReallocCf ZAllocator.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable.Q Require Import YW02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable.Q Require YT02_cf YT00_cf.
Import ListNotations.
Local Open Scope Z_scope.

Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Theorem zlib_realloc_contract_cf : forall pc, ms_realloc src0_msyms = Some pc -> realloc_contract_cf src0_msyms zlib_API pc.
Proof using.
  exact (realloc_contract_cf_ok src0_msyms zlib_API zlib_allocator_extra ltac:(vm_compute; reflexivity)
    (@YT02_cf.src0_realloc_realizes fx rc) realloc_safe).
Qed.

Theorem zlib_realloc_null_contract_cf : forall pc, ms_realloc src0_msyms = Some pc ->
  realloc_null_contract_cf src0_msyms zlib_API pc.
Proof using.
  exact (realloc_null_contract_cf_ok src0_msyms zlib_API zlib_allocator_extra ltac:(vm_compute; reflexivity)
    (@YT00_cf.src0_realloc_null_realizes fx rc)).
Qed.

End A.
