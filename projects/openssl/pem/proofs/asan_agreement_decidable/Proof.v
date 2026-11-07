From OSSVerify.openssl.pem Require Statements.
From OSSVerify.Proofs.openssl.pem.lib Require ConstAccept.

Theorem asan_agreement_decidable_holds : OSSVerify.openssl.pem.Statements.asan_agreement_decidable.
Proof. exact OSSVerify.Proofs.openssl.pem.lib.ConstAccept.asan_decidable. Qed.
