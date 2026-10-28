From OssFuzzTheorems.openssl.pem Require Statements.
From OssFuzzTheorems.Proofs.openssl.pem.lib Require Theorems.

Theorem asan_agrees_holds : OssFuzzTheorems.openssl.pem.Statements.asan_agrees.
Proof. exact OssFuzzTheorems.Proofs.openssl.pem.lib.Theorems.strong_universal_error_free_pem_asan. Qed.
