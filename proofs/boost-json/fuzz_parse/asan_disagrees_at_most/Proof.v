From Stdlib Require Import QArith.
From OssFuzzTheorems.boost_json.fuzz_parse Require Statements.
From OssFuzzTheorems.Proofs.boost_json.fuzz_parse.lib Require ConstAccept.

Theorem asan_disagrees_at_most_holds : OssFuzzTheorems.boost_json.fuzz_parse.Statements.asan_disagrees_at_most 0.
Proof. exact OssFuzzTheorems.Proofs.boost_json.fuzz_parse.lib.ConstAccept.asan_bound_0. Qed.
