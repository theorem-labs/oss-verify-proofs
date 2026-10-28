From OssFuzzTheorems.jsoncons.fuzz_json_cursor Require Statements.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require ConstAccept.

Theorem asan_agreement_decidable_holds : OssFuzzTheorems.jsoncons.fuzz_json_cursor.Statements.asan_agreement_decidable.
Proof. exact OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.ConstAccept.asan_decidable. Qed.
