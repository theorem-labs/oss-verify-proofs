From OSSVerify.jsoncons.fuzz_json_cursor Require Statements.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Theorems.

Theorem asan_halts_holds : OSSVerify.jsoncons.fuzz_json_cursor.Statements.asan_halts.
Proof. exact OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Theorems.halts_allowed_jsoncons_fuzz_json_cursor_halts_asan. Qed.
