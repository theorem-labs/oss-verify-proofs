From OSSVerify.openssl.bndiv Require Statements.
From OSSVerify.Proofs.openssl.bndiv.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.openssl.bndiv.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.openssl.bndiv.lib.Theorems.strong_universal_error_free_bndiv_ubsan. Qed.
