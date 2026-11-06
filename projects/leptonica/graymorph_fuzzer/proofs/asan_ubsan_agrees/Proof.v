From OSSVerify.leptonica.graymorph_fuzzer Require Statements.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OSSVerify.leptonica.graymorph_fuzzer.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Theorems.strong_universal_error_free_graymorph_fuzzer_both. Qed.
