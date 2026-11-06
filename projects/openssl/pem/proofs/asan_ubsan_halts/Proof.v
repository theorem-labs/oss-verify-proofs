From OSSVerify.openssl.pem Require Statements.
From OSSVerify.Proofs.openssl.pem.lib Require Theorems.

Theorem asan_ubsan_halts_holds : OSSVerify.openssl.pem.Statements.asan_ubsan_halts.
Proof. exact OSSVerify.Proofs.openssl.pem.lib.Theorems.halts_allowed_openssl_pem_halts_both. Qed.
