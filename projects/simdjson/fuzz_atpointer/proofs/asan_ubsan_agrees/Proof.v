From OSSVerify.simdjson.fuzz_atpointer Require Statements.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OSSVerify.simdjson.fuzz_atpointer.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Theorems.strong_universal_error_free_fuzz_atpointer_both. Qed.
