From OSSVerify.libreac.fuzz_knock Require Statements.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require Theorems.

Theorem plain_halts_may_fail_holds : OSSVerify.libreac.fuzz_knock.Statements.plain_halts_may_fail.
Proof. exact OSSVerify.Proofs.libreac.fuzz_knock.lib.Theorems.libreac_fuzz_knock_plain_halts_may_fail. Qed.
