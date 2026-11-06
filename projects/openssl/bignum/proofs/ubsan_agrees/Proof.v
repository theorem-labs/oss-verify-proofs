From OSSVerify.openssl.bignum Require Statements.
From OSSVerify.Proofs.openssl.bignum.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.openssl.bignum.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.openssl.bignum.lib.Theorems.strong_universal_error_free_bignum_ubsan. Qed.
