From OSSVerify.libreac.fuzz_knock Require Statements.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.libreac.fuzz_knock.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.libreac.fuzz_knock.lib.Theorems.libreac_fuzz_knock_ubsan_agrees. Qed.
