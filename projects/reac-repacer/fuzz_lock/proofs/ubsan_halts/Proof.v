From OSSVerify.reac_repacer.fuzz_lock Require Statements.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require Theorems.

Theorem ubsan_halts_holds : OSSVerify.reac_repacer.fuzz_lock.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Theorems.reac_repacer_fuzz_lock_ubsan_halts. Qed.
