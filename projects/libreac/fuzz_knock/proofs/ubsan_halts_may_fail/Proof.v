From OSSVerify.libreac.fuzz_knock Require Statements.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require Theorems.

Theorem ubsan_halts_may_fail_holds : OSSVerify.libreac.fuzz_knock.Statements.ubsan_halts_may_fail.
Proof. exact OSSVerify.Proofs.libreac.fuzz_knock.lib.Theorems.libreac_fuzz_knock_ubsan_halts_may_fail. Qed.
