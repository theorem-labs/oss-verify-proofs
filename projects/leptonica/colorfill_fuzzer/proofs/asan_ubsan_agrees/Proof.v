From OSSVerify.leptonica.colorfill_fuzzer Require Statements.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OSSVerify.leptonica.colorfill_fuzzer.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Theorems.strong_universal_error_free_colorfill_fuzzer_both. Qed.
