From OSSVerify.openssl.punycode Require Statements.
From OSSVerify.Proofs.openssl.punycode.lib Require ConstAccept.

Theorem asan_ubsan_agreement_decidable_holds : OSSVerify.openssl.punycode.Statements.asan_ubsan_agreement_decidable.
Proof. exact OSSVerify.Proofs.openssl.punycode.lib.ConstAccept.asan_ubsan_decidable. Qed.
