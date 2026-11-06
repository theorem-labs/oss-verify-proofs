From OSSVerify.bzip2.bzip2_compress_target Require Statements.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OSSVerify.bzip2.bzip2_compress_target.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Theorems.strong_universal_error_free_bzip2_compress_target_both. Qed.
