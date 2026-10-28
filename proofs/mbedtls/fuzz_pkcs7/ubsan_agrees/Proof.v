From OssFuzzTheorems.mbedtls.fuzz_pkcs7 Require Statements.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib Require Theorems.

Theorem ubsan_agrees_holds : OssFuzzTheorems.mbedtls.fuzz_pkcs7.Statements.ubsan_agrees.
Proof. exact OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Theorems.strong_universal_error_free_fuzz_pkcs7_ubsan. Qed.
