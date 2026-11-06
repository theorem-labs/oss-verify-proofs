From OSSVerify.openssl.bignum Require Statements.
From OSSVerify.Proofs.openssl.bignum.lib Require Theorems.

Theorem asan_ubsan_halts_holds : OSSVerify.openssl.bignum.Statements.asan_ubsan_halts.
Proof. exact OSSVerify.Proofs.openssl.bignum.lib.Theorems.halts_allowed_openssl_bignum_halts_both. Qed.
