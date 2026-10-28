From OssFuzzTheorems.openssl.pem Require Statements.
From OssFuzzTheorems.Proofs.openssl.pem.lib Require ConstAccept.

Theorem asan_ubsan_agreement_decidable_holds : OssFuzzTheorems.openssl.pem.Statements.asan_ubsan_agreement_decidable.
Proof. exact OssFuzzTheorems.Proofs.openssl.pem.lib.ConstAccept.asan_ubsan_decidable. Qed.
