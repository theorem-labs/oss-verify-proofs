From OSSVerify.cgif.cgif_rgb_fuzzer Require Statements.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Theorems.

Theorem asan_agrees_holds : OSSVerify.cgif.cgif_rgb_fuzzer.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib.Theorems.strong_universal_error_free_cgif_rgb_fuzzer_asan. Qed.
