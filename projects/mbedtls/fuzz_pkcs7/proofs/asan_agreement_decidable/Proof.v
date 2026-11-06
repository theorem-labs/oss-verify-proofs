From OSSVerify.mbedtls.fuzz_pkcs7 Require Statements.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib Require ConstAccept.

Theorem asan_agreement_decidable_holds : OSSVerify.mbedtls.fuzz_pkcs7.Statements.asan_agreement_decidable.
Proof. exact OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ConstAccept.asan_decidable. Qed.
