From OssFuzzTheorems.leptonica.grayquant_fuzzer Require Statements.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib Require Theorems.

Theorem ubsan_agrees_holds : OssFuzzTheorems.leptonica.grayquant_fuzzer.Statements.ubsan_agrees.
Proof. exact OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Theorems.strong_universal_error_free_grayquant_fuzzer_ubsan. Qed.
