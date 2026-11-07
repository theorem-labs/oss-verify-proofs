From OSSVerify.openssl.pem Require Statements.
From OSSVerify.Proofs.openssl.pem.lib Require ConstAccept.

Theorem ubsan_agreement_decidable_holds : OSSVerify.openssl.pem.Statements.ubsan_agreement_decidable.
Proof. exact OSSVerify.Proofs.openssl.pem.lib.ConstAccept.ubsan_decidable. Qed.
