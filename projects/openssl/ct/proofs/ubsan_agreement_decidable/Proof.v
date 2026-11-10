From OSSVerify.openssl.ct Require Statements.
From OSSVerify.Proofs.openssl.ct.lib Require ConstAccept.

Theorem ubsan_agreement_decidable_holds : OSSVerify.openssl.ct.Statements.ubsan_agreement_decidable.
Proof. exact OSSVerify.Proofs.openssl.ct.lib.ConstAccept.ubsan_decidable. Qed.
