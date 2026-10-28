From OssFuzzTheorems.cgif.cgif_file_fuzzer Require Statements.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Theorems.

Theorem asan_agrees_holds : OssFuzzTheorems.cgif.cgif_file_fuzzer.Statements.asan_agrees.
Proof. exact OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.Theorems.strong_universal_error_free_cgif_file_fuzzer_asan. Qed.
