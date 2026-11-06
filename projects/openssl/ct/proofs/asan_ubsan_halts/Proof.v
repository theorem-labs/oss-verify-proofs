From OSSVerify.openssl.ct Require Statements.
From OSSVerify.Proofs.openssl.ct.lib Require Theorems.

Theorem asan_ubsan_halts_holds : OSSVerify.openssl.ct.Statements.asan_ubsan_halts.
Proof. exact OSSVerify.Proofs.openssl.ct.lib.Theorems.halts_allowed_openssl_ct_halts_both. Qed.
