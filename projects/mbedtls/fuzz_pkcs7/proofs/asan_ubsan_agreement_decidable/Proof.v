From OSSVerify.mbedtls.fuzz_pkcs7 Require Statements.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib Require ConstAccept.

Theorem asan_ubsan_agreement_decidable_holds : OSSVerify.mbedtls.fuzz_pkcs7.Statements.asan_ubsan_agreement_decidable.
Proof. exact OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ConstAccept.asan_ubsan_decidable. Qed.
