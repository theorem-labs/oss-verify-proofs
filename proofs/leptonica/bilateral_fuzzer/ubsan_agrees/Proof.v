From OssFuzzTheorems.leptonica.bilateral_fuzzer Require Statements.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require Theorems.

Theorem ubsan_agrees_holds : OssFuzzTheorems.leptonica.bilateral_fuzzer.Statements.ubsan_agrees.
Proof. exact OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Theorems.strong_universal_error_free_bilateral_fuzzer_ubsan. Qed.
