From OSSVerify.openssl.hashtable Require Statements.
From OSSVerify.Proofs.openssl.hashtable.lib Require ConstAccept.

Theorem asan_ubsan_agreement_decidable_holds : OSSVerify.openssl.hashtable.Statements.asan_ubsan_agreement_decidable.
Proof. exact OSSVerify.Proofs.openssl.hashtable.lib.ConstAccept.asan_ubsan_decidable. Qed.
