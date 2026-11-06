From OSSVerify.openssl.bndiv Require Statements.
From OSSVerify.Proofs.openssl.bndiv.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OSSVerify.openssl.bndiv.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.openssl.bndiv.lib.Theorems.strong_universal_error_free_bndiv_both. Qed.
