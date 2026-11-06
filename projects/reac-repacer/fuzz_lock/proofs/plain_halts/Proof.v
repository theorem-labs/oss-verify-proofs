From OSSVerify.reac_repacer.fuzz_lock Require Statements.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require Theorems.

Theorem plain_halts_holds : OSSVerify.reac_repacer.fuzz_lock.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Theorems.reac_repacer_fuzz_lock_plain_halts. Qed.
