From OSSVerify.reac_repacer.fuzz_wire Require Statements.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Theorems.

Theorem asan_halts_holds : OSSVerify.reac_repacer.fuzz_wire.Statements.asan_halts.
Proof. exact OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Theorems.reac_repacer_fuzz_wire_asan_halts. Qed.
