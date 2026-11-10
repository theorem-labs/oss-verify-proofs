From OSSVerify.openssl.bndiv Require Statements.
From OSSVerify.Proofs.openssl.bndiv.lib Require ConstAccept.

Theorem asan_ubsan_agreement_decidable_holds : OSSVerify.openssl.bndiv.Statements.asan_ubsan_agreement_decidable.
Proof. exact OSSVerify.Proofs.openssl.bndiv.lib.ConstAccept.asan_ubsan_decidable. Qed.
