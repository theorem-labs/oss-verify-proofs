From OSSVerify.leptonica.grayquant_fuzzer Require Statements.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib Require Theorems.

Theorem asan_agrees_holds : OSSVerify.leptonica.grayquant_fuzzer.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Theorems.strong_universal_error_free_grayquant_fuzzer_asan. Qed.
