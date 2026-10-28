From OssFuzzTheorems.openssl.ct Require Statements.
From OssFuzzTheorems.Proofs.openssl.ct.lib Require Theorems.

Theorem asan_agrees_holds : OssFuzzTheorems.openssl.ct.Statements.asan_agrees.
Proof. exact OssFuzzTheorems.Proofs.openssl.ct.lib.Theorems.strong_universal_error_free_ct_asan. Qed.
