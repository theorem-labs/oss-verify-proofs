From OSSVerify.fast_float.from_chars Require Statements.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Theorems.

Theorem asan_ubsan_halts_holds : OSSVerify.fast_float.from_chars.Statements.asan_ubsan_halts.
Proof. exact OSSVerify.Proofs.fast_float.from_chars.lib.Theorems.halts_allowed_fast_float_from_chars_halts_both. Qed.
