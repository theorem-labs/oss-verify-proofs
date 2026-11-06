From OSSVerify.simdjson.fuzz_print_json Require Statements.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib Require Theorems.

Theorem asan_agrees_holds : OSSVerify.simdjson.fuzz_print_json.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Theorems.fuzz_print_json_asan_cfg. Qed.
