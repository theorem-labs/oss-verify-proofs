From OSSVerify.reac_repacer.fuzz_wire Require Statements.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Theorems.

Theorem ubsan_halts_holds : OSSVerify.reac_repacer.fuzz_wire.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Theorems.reac_repacer_fuzz_wire_ubsan_halts. Qed.
