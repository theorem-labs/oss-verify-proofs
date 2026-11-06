From OSSVerify.simdjson.fuzz_print_json Require Statements.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.simdjson.fuzz_print_json.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Theorems.fuzz_print_json_ubsan_cfg. Qed.
