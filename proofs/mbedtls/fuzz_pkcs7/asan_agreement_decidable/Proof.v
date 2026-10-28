From OssFuzzTheorems.mbedtls.fuzz_pkcs7 Require Statements.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib Require ConstAccept.

Theorem asan_agreement_decidable_holds : OssFuzzTheorems.mbedtls.fuzz_pkcs7.Statements.asan_agreement_decidable.
Proof. exact OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ConstAccept.asan_decidable. Qed.
