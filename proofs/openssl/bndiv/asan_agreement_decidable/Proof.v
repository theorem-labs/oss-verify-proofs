From OssFuzzTheorems.openssl.bndiv Require Statements.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib Require ConstAccept.

Theorem asan_agreement_decidable_holds : OssFuzzTheorems.openssl.bndiv.Statements.asan_agreement_decidable.
Proof. exact OssFuzzTheorems.Proofs.openssl.bndiv.lib.ConstAccept.asan_decidable. Qed.
