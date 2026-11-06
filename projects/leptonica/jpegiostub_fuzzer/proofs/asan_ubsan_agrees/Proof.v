From OSSVerify.leptonica.jpegiostub_fuzzer Require Statements.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OSSVerify.leptonica.jpegiostub_fuzzer.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Theorems.strong_universal_error_free_jpegiostub_fuzzer_both. Qed.
