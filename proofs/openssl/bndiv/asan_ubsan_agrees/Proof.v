From OssFuzzTheorems.openssl.bndiv Require Statements.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OssFuzzTheorems.openssl.bndiv.Statements.asan_ubsan_agrees.
Proof. exact OssFuzzTheorems.Proofs.openssl.bndiv.lib.Theorems.strong_universal_error_free_bndiv_both. Qed.
