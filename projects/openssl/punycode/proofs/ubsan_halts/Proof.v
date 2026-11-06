From OSSVerify.openssl.punycode Require Statements.
From OSSVerify.Proofs.openssl.punycode.lib Require Theorems.

Theorem ubsan_halts_holds : OSSVerify.openssl.punycode.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.openssl.punycode.lib.Theorems.halts_allowed_openssl_punycode_halts_ubsan. Qed.
