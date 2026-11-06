From OSSVerify.openssl.bignum Require Statements.
From OSSVerify.Proofs.openssl.bignum.lib Require Theorems.

Theorem plain_halts_holds : OSSVerify.openssl.bignum.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.openssl.bignum.lib.Theorems.halts_allowed_openssl_bignum_halts_plain. Qed.
