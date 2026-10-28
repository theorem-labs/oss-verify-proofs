From OssFuzzTheorems.openssl.echconfiglist_parser Require Statements.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OssFuzzTheorems.openssl.echconfiglist_parser.Statements.asan_ubsan_agrees.
Proof. exact OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Theorems.strong_universal_error_free_echconfiglist_parser_both. Qed.
