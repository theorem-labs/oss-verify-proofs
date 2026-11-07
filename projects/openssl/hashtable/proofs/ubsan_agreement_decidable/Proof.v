From OSSVerify.openssl.hashtable Require Statements.
From OSSVerify.Proofs.openssl.hashtable.lib Require ConstAccept.

Theorem ubsan_agreement_decidable_holds : OSSVerify.openssl.hashtable.Statements.ubsan_agreement_decidable.
Proof. exact OSSVerify.Proofs.openssl.hashtable.lib.ConstAccept.ubsan_decidable. Qed.
