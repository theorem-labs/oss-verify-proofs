From OSSVerify.openssl.echconfiglist_parser Require Statements.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Theorems.

Theorem asan_agrees_holds : OSSVerify.openssl.echconfiglist_parser.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Theorems.strong_universal_error_free_echconfiglist_parser_asan. Qed.
