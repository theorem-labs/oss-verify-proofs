From OSSVerify.cgif.cgif_file_fuzzer Require Statements.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.cgif.cgif_file_fuzzer.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib.Theorems.strong_universal_error_free_cgif_file_fuzzer_ubsan. Qed.
