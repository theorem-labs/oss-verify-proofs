From OSSVerify.openssl.bignum Require Statements.
From OSSVerify.Proofs.openssl.bignum.lib Require Theorems.

Theorem asan_agrees_holds : OSSVerify.openssl.bignum.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.openssl.bignum.lib.Theorems.strong_universal_error_free_bignum_asan. Qed.
