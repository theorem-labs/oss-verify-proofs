From OSSVerify.openssl.pem Require Statements.
From OSSVerify.Proofs.openssl.pem.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OSSVerify.openssl.pem.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.openssl.pem.lib.Theorems.strong_universal_error_free_pem_both. Qed.
