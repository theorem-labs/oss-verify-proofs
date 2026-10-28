From OssFuzzTheorems.openssl.punycode Require Statements.
From OssFuzzTheorems.Proofs.openssl.punycode.lib Require ConstAccept.

Theorem asan_ubsan_agreement_decidable_holds : OssFuzzTheorems.openssl.punycode.Statements.asan_ubsan_agreement_decidable.
Proof. exact OssFuzzTheorems.Proofs.openssl.punycode.lib.ConstAccept.asan_ubsan_decidable. Qed.
