From OSSVerify.openssl.ct Require Statements.
From OSSVerify.Proofs.openssl.ct.lib Require ConstAccept.

Theorem asan_agreement_decidable_holds : OSSVerify.openssl.ct.Statements.asan_agreement_decidable.
Proof. exact OSSVerify.Proofs.openssl.ct.lib.ConstAccept.asan_decidable. Qed.
