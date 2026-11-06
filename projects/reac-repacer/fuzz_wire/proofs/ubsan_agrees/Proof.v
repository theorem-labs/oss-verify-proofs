From OSSVerify.reac_repacer.fuzz_wire Require Statements.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.reac_repacer.fuzz_wire.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Theorems.reac_repacer_fuzz_wire_ubsan_agrees. Qed.
