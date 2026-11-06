From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YK11 YM05 YO0d YH02 YN2b.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Contract SlotAgree ZAllocator AllocCallocCf CallocCert_cf.
Local Open Scope Z_scope.

Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Theorem zlib_calloc_contract_cf : forall pc, calloc_contract_cf src0_msyms zlib_API pc.
Proof using.
  exact (calloc_contract_cf_ok src0_msyms zlib_API zlib_allocator_extra ltac:(vm_compute; reflexivity)
    (@src0_calloc_realizes_cf fx rc)).
Qed.

End A.
