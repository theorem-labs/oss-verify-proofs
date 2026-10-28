From OssFuzzTheorems.leptonica.pix_orient_fuzzer Require Statements.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib Require Theorems.

Theorem ubsan_agrees_holds : OssFuzzTheorems.leptonica.pix_orient_fuzzer.Statements.ubsan_agrees.
Proof. exact OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Theorems.strong_universal_error_free_pix_orient_fuzzer_ubsan. Qed.
