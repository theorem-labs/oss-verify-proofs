From OSSVerify.libreac.fuzz_boxreg Require Statements.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Theorems.

Theorem plain_halts_holds : OSSVerify.libreac.fuzz_boxreg.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Theorems.libreac_fuzz_boxreg_plain_halts. Qed.
