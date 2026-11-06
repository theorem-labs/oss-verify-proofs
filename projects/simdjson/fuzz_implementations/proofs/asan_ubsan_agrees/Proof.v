From OSSVerify.simdjson.fuzz_implementations Require Statements.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OSSVerify.simdjson.fuzz_implementations.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Theorems.strong_universal_error_free_fuzz_implementations_both. Qed.
