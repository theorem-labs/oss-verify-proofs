From OSSVerify.leptonica.paintcmap_fuzzer Require Statements.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OSSVerify.leptonica.paintcmap_fuzzer.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Theorems.strong_universal_error_free_paintcmap_fuzzer_both. Qed.
