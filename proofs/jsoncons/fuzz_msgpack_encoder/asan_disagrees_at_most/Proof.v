From Stdlib Require Import QArith.
From OssFuzzTheorems.jsoncons.fuzz_msgpack_encoder Require Statements.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require ConstAccept.

Theorem asan_disagrees_at_most_holds : OssFuzzTheorems.jsoncons.fuzz_msgpack_encoder.Statements.asan_disagrees_at_most 0.
Proof. exact OssFuzzTheorems.Proofs.jsoncons.fuzz_msgpack_encoder.lib.ConstAccept.asan_bound_0. Qed.
