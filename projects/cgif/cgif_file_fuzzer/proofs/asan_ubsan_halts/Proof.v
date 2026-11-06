From OSSVerify.cgif.cgif_file_fuzzer Require Statements.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Theorems.

Theorem asan_ubsan_halts_holds : OSSVerify.cgif.cgif_file_fuzzer.Statements.asan_ubsan_halts.
Proof. exact OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib.Theorems.halts_allowed_cgif_cgif_file_fuzzer_halts_both. Qed.
