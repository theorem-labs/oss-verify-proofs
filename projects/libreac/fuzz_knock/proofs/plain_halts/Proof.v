From OSSVerify.libreac.fuzz_knock Require Statements.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require Theorems.

Theorem plain_halts_holds : OSSVerify.libreac.fuzz_knock.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.libreac.fuzz_knock.lib.Theorems.libreac_fuzz_knock_plain_halts. Qed.
