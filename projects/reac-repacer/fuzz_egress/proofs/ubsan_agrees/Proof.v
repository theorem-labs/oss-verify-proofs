From OSSVerify.reac_repacer.fuzz_egress Require Statements.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.reac_repacer.fuzz_egress.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Theorems.reac_repacer_fuzz_egress_ubsan_agrees. Qed.
