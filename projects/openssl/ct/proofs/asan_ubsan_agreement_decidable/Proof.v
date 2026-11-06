From OSSVerify.openssl.ct Require Statements.
From OSSVerify.Proofs.openssl.ct.lib Require ConstAccept.

Theorem asan_ubsan_agreement_decidable_holds : OSSVerify.openssl.ct.Statements.asan_ubsan_agreement_decidable.
Proof. exact OSSVerify.Proofs.openssl.ct.lib.ConstAccept.asan_ubsan_decidable. Qed.
