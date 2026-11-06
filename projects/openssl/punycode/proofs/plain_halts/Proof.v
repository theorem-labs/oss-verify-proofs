From OSSVerify.openssl.punycode Require Statements.
From OSSVerify.Proofs.openssl.punycode.lib Require Theorems.

Theorem plain_halts_holds : OSSVerify.openssl.punycode.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.openssl.punycode.lib.Theorems.halts_allowed_openssl_punycode_halts_plain. Qed.
