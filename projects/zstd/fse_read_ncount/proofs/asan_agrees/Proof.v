From OSSVerify.zstd.fse_read_ncount Require Statements.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib Require Theorems.

Theorem asan_agrees_holds : OSSVerify.zstd.fse_read_ncount.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.zstd.fse_read_ncount.lib.Theorems.strong_universal_error_free_fse_read_ncount_asan. Qed.
