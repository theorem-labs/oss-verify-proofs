From OSSVerify.cgif.cgif_rgb_fuzzer Require Statements.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Theorems.

Theorem asan_ubsan_halts_holds : OSSVerify.cgif.cgif_rgb_fuzzer.Statements.asan_ubsan_halts.
Proof. exact OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib.Theorems.halts_allowed_cgif_cgif_rgb_fuzzer_halts_both. Qed.
