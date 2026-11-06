From OSSVerify.openssl.punycode Require Statements.
From OSSVerify.Proofs.openssl.punycode.lib Require Theorems.

Theorem asan_agrees_holds : OSSVerify.openssl.punycode.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.openssl.punycode.lib.Theorems.strong_universal_error_free_punycode_asan. Qed.
