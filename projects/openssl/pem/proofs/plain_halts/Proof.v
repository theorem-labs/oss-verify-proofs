From OSSVerify.openssl.pem Require Statements.
From OSSVerify.Proofs.openssl.pem.lib Require Theorems.

Theorem plain_halts_holds : OSSVerify.openssl.pem.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.openssl.pem.lib.Theorems.halts_allowed_openssl_pem_halts_plain. Qed.
