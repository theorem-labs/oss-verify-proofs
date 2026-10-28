From OssFuzzTheorems.openssl.ct Require Statements.
From OssFuzzTheorems.Proofs.openssl.ct.lib Require Theorems.

Theorem ubsan_agrees_holds : OssFuzzTheorems.openssl.ct.Statements.ubsan_agrees.
Proof. exact OssFuzzTheorems.Proofs.openssl.ct.lib.Theorems.strong_universal_error_free_ct_ubsan. Qed.
