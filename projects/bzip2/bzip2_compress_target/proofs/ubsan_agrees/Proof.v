From OSSVerify.bzip2.bzip2_compress_target Require Statements.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.bzip2.bzip2_compress_target.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Theorems.strong_universal_error_free_bzip2_compress_target_ubsan. Qed.
