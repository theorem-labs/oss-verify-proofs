From OSSVerify.fast_float.from_chars Require Statements.
From OSSVerify.Proofs.fast_float.from_chars.lib Require ConstAccept.

Theorem asan_ubsan_agreement_decidable_holds : OSSVerify.fast_float.from_chars.Statements.asan_ubsan_agreement_decidable.
Proof. exact OSSVerify.Proofs.fast_float.from_chars.lib.ConstAccept.asan_ubsan_decidable. Qed.
