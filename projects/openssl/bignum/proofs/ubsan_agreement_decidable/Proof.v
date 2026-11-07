From OSSVerify.openssl.bignum Require Statements.
From OSSVerify.Proofs.openssl.bignum.lib Require ConstAccept.

Theorem ubsan_agreement_decidable_holds : OSSVerify.openssl.bignum.Statements.ubsan_agreement_decidable.
Proof. exact OSSVerify.Proofs.openssl.bignum.lib.ConstAccept.ubsan_decidable. Qed.
