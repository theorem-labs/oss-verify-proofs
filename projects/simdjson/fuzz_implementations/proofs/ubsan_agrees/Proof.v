From OSSVerify.simdjson.fuzz_implementations Require Statements.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.simdjson.fuzz_implementations.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Theorems.strong_universal_error_free_fuzz_implementations_ubsan. Qed.
