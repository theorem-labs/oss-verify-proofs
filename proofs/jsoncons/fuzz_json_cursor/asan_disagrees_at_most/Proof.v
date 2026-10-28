From Stdlib Require Import QArith.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor Require Statements.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require ConstAccept.

Theorem asan_disagrees_at_most_holds : OssFuzzTheorems.jsoncons.fuzz_json_cursor.Statements.asan_disagrees_at_most 0.
Proof. exact OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.ConstAccept.asan_bound_0. Qed.
