From OSSVerify.openssl.pem Require Statements.
From OSSVerify.Proofs.openssl.pem.lib Require ConstAccept.

Theorem asan_ubsan_agreement_decidable_holds : OSSVerify.openssl.pem.Statements.asan_ubsan_agreement_decidable.
Proof. exact OSSVerify.Proofs.openssl.pem.lib.ConstAccept.asan_ubsan_decidable. Qed.
