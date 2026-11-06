From OSSVerify.libreac.fuzz_boxreg Require Statements.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OSSVerify.libreac.fuzz_boxreg.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Theorems.libreac_fuzz_boxreg_asan_ubsan_agrees. Qed.
