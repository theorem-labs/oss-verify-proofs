From OSSVerify.jsoncons.fuzz_json_cursor Require Statements.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OSSVerify.jsoncons.fuzz_json_cursor.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Theorems.strong_universal_error_free_fuzz_json_cursor_both. Qed.
