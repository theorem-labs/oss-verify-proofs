From OSSVerify.simdjson.fuzz_ondemand Require Statements.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OSSVerify.simdjson.fuzz_ondemand.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Theorems.strong_universal_error_free_fuzz_ondemand_both. Qed.
