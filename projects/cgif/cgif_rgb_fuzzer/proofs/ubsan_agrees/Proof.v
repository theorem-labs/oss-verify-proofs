From OSSVerify.cgif.cgif_rgb_fuzzer Require Statements.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.cgif.cgif_rgb_fuzzer.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib.Theorems.strong_universal_error_free_cgif_rgb_fuzzer_ubsan. Qed.
