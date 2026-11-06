From OSSVerify.fast_float.from_chars Require Statements.
From OSSVerify.Proofs.fast_float.from_chars.lib Require ConstAccept.

Theorem ubsan_agreement_decidable_holds : OSSVerify.fast_float.from_chars.Statements.ubsan_agreement_decidable.
Proof. exact OSSVerify.Proofs.fast_float.from_chars.lib.ConstAccept.ubsan_decidable. Qed.
