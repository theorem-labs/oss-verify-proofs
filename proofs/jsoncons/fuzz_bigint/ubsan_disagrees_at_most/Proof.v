From Stdlib Require Import QArith.
From OssFuzzTheorems.jsoncons.fuzz_bigint Require Statements.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bigint.lib Require ConstAccept.

Theorem ubsan_disagrees_at_most_holds : OssFuzzTheorems.jsoncons.fuzz_bigint.Statements.ubsan_disagrees_at_most 0.
Proof. exact OssFuzzTheorems.Proofs.jsoncons.fuzz_bigint.lib.ConstAccept.ubsan_bound_0. Qed.
