From OSSVerify.openssl.bignum Require Statements.
From OSSVerify.Proofs.openssl.bignum.lib Require ConstAccept.

Theorem asan_agreement_decidable_holds : OSSVerify.openssl.bignum.Statements.asan_agreement_decidable.
Proof. exact OSSVerify.Proofs.openssl.bignum.lib.ConstAccept.asan_decidable. Qed.
