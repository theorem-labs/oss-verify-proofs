From OSSVerify.libreac.fuzz_boxreg Require Statements.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Theorems.

Theorem ubsan_halts_holds : OSSVerify.libreac.fuzz_boxreg.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Theorems.libreac_fuzz_boxreg_ubsan_halts. Qed.
