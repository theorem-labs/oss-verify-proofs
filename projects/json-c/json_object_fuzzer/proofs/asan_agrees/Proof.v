From OSSVerify.json_c.json_object_fuzzer Require Statements.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Theorems.

Theorem asan_agrees_holds : OSSVerify.json_c.json_object_fuzzer.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Theorems.strong_universal_error_free_json_object_fuzzer_asan. Qed.
