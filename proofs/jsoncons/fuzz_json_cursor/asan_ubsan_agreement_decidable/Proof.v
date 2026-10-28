From OssFuzzTheorems.jsoncons.fuzz_json_cursor Require Statements.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require ConstAccept.

Theorem asan_ubsan_agreement_decidable_holds : OssFuzzTheorems.jsoncons.fuzz_json_cursor.Statements.asan_ubsan_agreement_decidable.
Proof. exact OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.ConstAccept.asan_ubsan_decidable. Qed.
