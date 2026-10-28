From OssFuzzTheorems.json_c.json_object_fuzzer Require Statements.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Theorems.

Theorem ubsan_agrees_holds : OssFuzzTheorems.json_c.json_object_fuzzer.Statements.ubsan_agrees.
Proof. exact OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Theorems.strong_universal_error_free_json_object_fuzzer_ubsan. Qed.
