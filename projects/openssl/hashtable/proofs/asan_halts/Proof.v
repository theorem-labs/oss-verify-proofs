From OSSVerify.openssl.hashtable Require Statements.
From OSSVerify.Proofs.openssl.hashtable.lib Require Theorems.

Theorem asan_halts_holds : OSSVerify.openssl.hashtable.Statements.asan_halts.
Proof. exact OSSVerify.Proofs.openssl.hashtable.lib.Theorems.halts_allowed_openssl_hashtable_halts_asan. Qed.
