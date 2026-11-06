From OSSVerify.mbedtls.fuzz_pkcs7 Require Statements.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OSSVerify.mbedtls.fuzz_pkcs7.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Theorems.strong_universal_error_free_fuzz_pkcs7_both. Qed.
