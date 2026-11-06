From OSSVerify.leptonica.pix1_fuzzer Require Statements.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib Require Theorems.

Theorem asan_agrees_holds : OSSVerify.leptonica.pix1_fuzzer.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Theorems.strong_universal_error_free_pix1_fuzzer_asan. Qed.
