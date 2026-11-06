From OSSVerify.fast_float.from_chars Require Statements.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OSSVerify.fast_float.from_chars.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.fast_float.from_chars.lib.Theorems.strong_universal_error_free_from_chars_both. Qed.
