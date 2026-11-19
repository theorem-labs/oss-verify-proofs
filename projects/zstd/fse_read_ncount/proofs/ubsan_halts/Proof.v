From OSSVerify.zstd.fse_read_ncount Require Statements.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib Require HaltsUbsanB.

Theorem ubsan_halts_holds : OSSVerify.zstd.fse_read_ncount.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.zstd.fse_read_ncount.lib.HaltsUbsanB.halts_ubsanB_fo. Qed.
