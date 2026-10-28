From OssFuzzTheorems.openssl.echconfiglist_parser Require Statements.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require ConstAccept.

Theorem ubsan_agreement_decidable_holds : OssFuzzTheorems.openssl.echconfiglist_parser.Statements.ubsan_agreement_decidable.
Proof. exact OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.ConstAccept.ubsan_decidable. Qed.
