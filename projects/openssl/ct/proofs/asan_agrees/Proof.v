From OSSVerify.openssl.ct Require Statements.
From OSSVerify.Proofs.openssl.ct.lib Require Theorems.

Theorem asan_agrees_holds : OSSVerify.openssl.ct.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.openssl.ct.lib.Theorems.strong_universal_error_free_ct_asan. Qed.
