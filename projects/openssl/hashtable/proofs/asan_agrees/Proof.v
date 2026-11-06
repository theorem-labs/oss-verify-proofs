From OSSVerify.openssl.hashtable Require Statements.
From OSSVerify.Proofs.openssl.hashtable.lib Require Theorems.

Theorem asan_agrees_holds : OSSVerify.openssl.hashtable.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.openssl.hashtable.lib.Theorems.strong_universal_error_free_hashtable_asan. Qed.
