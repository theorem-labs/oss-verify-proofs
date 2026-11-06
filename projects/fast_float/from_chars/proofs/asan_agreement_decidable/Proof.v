From OSSVerify.fast_float.from_chars Require Statements.
From OSSVerify.Proofs.fast_float.from_chars.lib Require ConstAccept.

Theorem asan_agreement_decidable_holds : OSSVerify.fast_float.from_chars.Statements.asan_agreement_decidable.
Proof. exact OSSVerify.Proofs.fast_float.from_chars.lib.ConstAccept.asan_decidable. Qed.
