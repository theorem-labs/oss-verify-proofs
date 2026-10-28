From OssFuzzTheorems.openssl.echconfiglist_parser Require Statements.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require ConstAccept.

Theorem asan_agreement_decidable_holds : OssFuzzTheorems.openssl.echconfiglist_parser.Statements.asan_agreement_decidable.
Proof. exact OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.ConstAccept.asan_decidable. Qed.
