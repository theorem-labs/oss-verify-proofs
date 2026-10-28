From OssFuzzTheorems.jsoncons.fuzz_msgpack_encoder Require Statements.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require ConstAccept.

Theorem asan_agreement_decidable_holds : OssFuzzTheorems.jsoncons.fuzz_msgpack_encoder.Statements.asan_agreement_decidable.
Proof. exact OssFuzzTheorems.Proofs.jsoncons.fuzz_msgpack_encoder.lib.ConstAccept.asan_decidable. Qed.
