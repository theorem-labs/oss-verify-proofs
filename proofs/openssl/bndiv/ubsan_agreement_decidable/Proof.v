From OssFuzzTheorems.openssl.bndiv Require Statements.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib Require ConstAccept.

Theorem ubsan_agreement_decidable_holds : OssFuzzTheorems.openssl.bndiv.Statements.ubsan_agreement_decidable.
Proof. exact OssFuzzTheorems.Proofs.openssl.bndiv.lib.ConstAccept.ubsan_decidable. Qed.
