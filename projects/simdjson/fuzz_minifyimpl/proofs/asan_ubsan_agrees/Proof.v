From OSSVerify.simdjson.fuzz_minifyimpl Require Statements.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OSSVerify.simdjson.fuzz_minifyimpl.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Theorems.strong_universal_error_free_fuzz_minifyimpl_both. Qed.
