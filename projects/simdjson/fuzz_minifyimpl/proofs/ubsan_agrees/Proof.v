From OSSVerify.simdjson.fuzz_minifyimpl Require Statements.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.simdjson.fuzz_minifyimpl.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Theorems.strong_universal_error_free_fuzz_minifyimpl_ubsan. Qed.
