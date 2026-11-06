From OSSVerify.openssl.bndiv Require Statements.
From OSSVerify.Proofs.openssl.bndiv.lib Require Theorems.

Theorem plain_halts_holds : OSSVerify.openssl.bndiv.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.openssl.bndiv.lib.Theorems.halts_allowed_openssl_bndiv_halts_plain. Qed.
