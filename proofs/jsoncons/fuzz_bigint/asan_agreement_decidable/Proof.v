From OssFuzzTheorems.jsoncons.fuzz_bigint Require Statements.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bigint.lib Require ConstAccept.

Theorem asan_agreement_decidable_holds : OssFuzzTheorems.jsoncons.fuzz_bigint.Statements.asan_agreement_decidable.
Proof. exact OssFuzzTheorems.Proofs.jsoncons.fuzz_bigint.lib.ConstAccept.asan_decidable. Qed.
