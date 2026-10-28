From OssFuzzTheorems.openssl.ct Require Statements.
From OssFuzzTheorems.Proofs.openssl.ct.lib Require ConstAccept.

Theorem asan_ubsan_agreement_decidable_holds : OssFuzzTheorems.openssl.ct.Statements.asan_ubsan_agreement_decidable.
Proof. exact OssFuzzTheorems.Proofs.openssl.ct.lib.ConstAccept.asan_ubsan_decidable. Qed.
