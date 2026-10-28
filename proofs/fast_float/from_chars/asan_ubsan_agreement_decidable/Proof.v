From OssFuzzTheorems.fast_float.from_chars Require Statements.
From OssFuzzTheorems.Proofs.fast_float.from_chars.lib Require ConstAccept.

Theorem asan_ubsan_agreement_decidable_holds : OssFuzzTheorems.fast_float.from_chars.Statements.asan_ubsan_agreement_decidable.
Proof. exact OssFuzzTheorems.Proofs.fast_float.from_chars.lib.ConstAccept.asan_ubsan_decidable. Qed.
