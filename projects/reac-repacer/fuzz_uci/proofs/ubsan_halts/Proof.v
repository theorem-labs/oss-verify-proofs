From OSSVerify.reac_repacer.fuzz_uci Require Statements.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib Require Theorems.

Theorem ubsan_halts_holds : OSSVerify.reac_repacer.fuzz_uci.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Theorems.reac_repacer_fuzz_uci_ubsan_halts. Qed.
