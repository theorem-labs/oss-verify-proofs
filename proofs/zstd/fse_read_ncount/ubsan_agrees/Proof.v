From OssFuzzTheorems.zstd.fse_read_ncount Require Statements.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib Require Theorems.

Theorem ubsan_agrees_holds : OssFuzzTheorems.zstd.fse_read_ncount.Statements.ubsan_agrees.
Proof. exact OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Theorems.strong_universal_error_free_fse_read_ncount_ubsan. Qed.
