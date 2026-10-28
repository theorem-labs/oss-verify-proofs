From OssFuzzTheorems.openssl.bignum Require Statements.
From OssFuzzTheorems.Proofs.openssl.bignum.lib Require ConstAccept.

Theorem asan_ubsan_agreement_decidable_holds : OssFuzzTheorems.openssl.bignum.Statements.asan_ubsan_agreement_decidable.
Proof. exact OssFuzzTheorems.Proofs.openssl.bignum.lib.ConstAccept.asan_ubsan_decidable. Qed.
