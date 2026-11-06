From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YM05 YO0d YH02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Contract SlotAgree ZAllocator.
Local Open Scope Z_scope.

Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* This build's allocator has no calloc (ms_calloc src0_msyms = None). *)
Theorem zlib_calloc_contract_cf : forall pc, calloc_contract_cf src0_msyms zlib_API pc.
Proof using. intros pc L A regs mem md m n b _ _ _ _ _ _ _ Hpc. cbv [ms_calloc src0_msyms] in Hpc. discriminate Hpc. Qed.

End A.
