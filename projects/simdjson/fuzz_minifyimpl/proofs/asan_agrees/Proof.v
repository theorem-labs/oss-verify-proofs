From OSSVerify.simdjson.fuzz_minifyimpl Require Statements.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib Require Theorems.

Theorem asan_agrees_holds : OSSVerify.simdjson.fuzz_minifyimpl.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Theorems.strong_universal_error_free_fuzz_minifyimpl_asan. Qed.
