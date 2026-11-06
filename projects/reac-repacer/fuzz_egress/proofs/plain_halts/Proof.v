From OSSVerify.reac_repacer.fuzz_egress Require Statements.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require Theorems.

Theorem plain_halts_holds : OSSVerify.reac_repacer.fuzz_egress.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Theorems.reac_repacer_fuzz_egress_plain_halts. Qed.
