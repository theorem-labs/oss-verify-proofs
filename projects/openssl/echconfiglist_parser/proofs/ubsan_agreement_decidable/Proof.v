From OSSVerify.openssl.echconfiglist_parser Require Statements.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require ConstAccept.

Theorem ubsan_agreement_decidable_holds : OSSVerify.openssl.echconfiglist_parser.Statements.ubsan_agreement_decidable.
Proof. exact OSSVerify.Proofs.openssl.echconfiglist_parser.lib.ConstAccept.ubsan_decidable. Qed.
