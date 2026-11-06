From OSSVerify.openssl.echconfiglist_parser Require Statements.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Theorems.

Theorem ubsan_halts_holds : OSSVerify.openssl.echconfiglist_parser.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Theorems.halts_allowed_openssl_echconfiglist_parser_halts_ubsan. Qed.
