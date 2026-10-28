From OssFuzzTheorems.openssl.bignum Require Statements.
From OssFuzzTheorems.Proofs.openssl.bignum.lib Require ConstAccept.

Theorem asan_agreement_decidable_holds : OssFuzzTheorems.openssl.bignum.Statements.asan_agreement_decidable.
Proof. exact OssFuzzTheorems.Proofs.openssl.bignum.lib.ConstAccept.asan_decidable. Qed.
