From OSSVerify.openssl.bndiv Require Statements.
From OSSVerify.Proofs.openssl.bndiv.lib Require ConstAccept.

Theorem ubsan_agreement_decidable_holds : OSSVerify.openssl.bndiv.Statements.ubsan_agreement_decidable.
Proof. exact OSSVerify.Proofs.openssl.bndiv.lib.ConstAccept.ubsan_decidable. Qed.
