From OSSVerify.openssl.echconfiglist_parser Require Statements.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require ConstAccept.

Theorem asan_agreement_decidable_holds : OSSVerify.openssl.echconfiglist_parser.Statements.asan_agreement_decidable.
Proof. exact OSSVerify.Proofs.openssl.echconfiglist_parser.lib.ConstAccept.asan_decidable. Qed.
