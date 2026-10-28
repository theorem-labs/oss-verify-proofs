From Stdlib Require Import QArith.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max Require Statements.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require ConstAccept.

Theorem asan_disagrees_at_most_holds : OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.Statements.asan_disagrees_at_most 0.
Proof. exact OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.ConstAccept.asan_bound_0. Qed.
