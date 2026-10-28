From OssFuzzTheorems.jsoncons.fuzz_bigint Require Statements.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bigint.lib Require ConstAccept.

Theorem ubsan_agreement_decidable_holds : OssFuzzTheorems.jsoncons.fuzz_bigint.Statements.ubsan_agreement_decidable.
Proof. exact OssFuzzTheorems.Proofs.jsoncons.fuzz_bigint.lib.ConstAccept.ubsan_decidable. Qed.
