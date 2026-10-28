From OssFuzzTheorems.openssl.hashtable Require Statements.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OssFuzzTheorems.openssl.hashtable.Statements.asan_ubsan_agrees.
Proof. exact OssFuzzTheorems.Proofs.openssl.hashtable.lib.Theorems.strong_universal_error_free_hashtable_both. Qed.
