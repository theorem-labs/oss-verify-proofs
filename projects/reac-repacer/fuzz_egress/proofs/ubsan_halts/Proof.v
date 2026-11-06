From OSSVerify.reac_repacer.fuzz_egress Require Statements.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require Theorems.

Theorem ubsan_halts_holds : OSSVerify.reac_repacer.fuzz_egress.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Theorems.reac_repacer_fuzz_egress_ubsan_halts. Qed.
