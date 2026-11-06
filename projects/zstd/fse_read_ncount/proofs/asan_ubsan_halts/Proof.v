From OSSVerify.zstd.fse_read_ncount Require Statements.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib Require Theorems.

Theorem asan_ubsan_halts_holds : OSSVerify.zstd.fse_read_ncount.Statements.asan_ubsan_halts.
Proof. exact OSSVerify.Proofs.zstd.fse_read_ncount.lib.Theorems.halts_allowed_zstd_fse_read_ncount_halts_both. Qed.
