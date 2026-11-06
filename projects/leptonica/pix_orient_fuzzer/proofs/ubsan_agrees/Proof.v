From OSSVerify.leptonica.pix_orient_fuzzer Require Statements.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.leptonica.pix_orient_fuzzer.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Theorems.strong_universal_error_free_pix_orient_fuzzer_ubsan. Qed.
