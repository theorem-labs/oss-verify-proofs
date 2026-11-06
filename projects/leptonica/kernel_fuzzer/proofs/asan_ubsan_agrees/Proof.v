From OSSVerify.leptonica.kernel_fuzzer Require Statements.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OSSVerify.leptonica.kernel_fuzzer.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Theorems.strong_universal_error_free_kernel_fuzzer_both. Qed.
