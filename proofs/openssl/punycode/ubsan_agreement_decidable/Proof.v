From OssFuzzTheorems.openssl.punycode Require Statements.
From OssFuzzTheorems.Proofs.openssl.punycode.lib Require ConstAccept.

Theorem ubsan_agreement_decidable_holds : OssFuzzTheorems.openssl.punycode.Statements.ubsan_agreement_decidable.
Proof. exact OssFuzzTheorems.Proofs.openssl.punycode.lib.ConstAccept.ubsan_decidable. Qed.
