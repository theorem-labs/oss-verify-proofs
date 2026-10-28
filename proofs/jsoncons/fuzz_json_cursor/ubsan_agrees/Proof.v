From OssFuzzTheorems.jsoncons.fuzz_json_cursor Require Statements.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Theorems.

Theorem ubsan_agrees_holds : OssFuzzTheorems.jsoncons.fuzz_json_cursor.Statements.ubsan_agrees.
Proof. exact OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.Theorems.strong_universal_error_free_fuzz_json_cursor_ubsan. Qed.
