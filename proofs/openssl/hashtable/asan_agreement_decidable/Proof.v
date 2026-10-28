From OssFuzzTheorems.openssl.hashtable Require Statements.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require ConstAccept.

Theorem asan_agreement_decidable_holds : OssFuzzTheorems.openssl.hashtable.Statements.asan_agreement_decidable.
Proof. exact OssFuzzTheorems.Proofs.openssl.hashtable.lib.ConstAccept.asan_decidable. Qed.
