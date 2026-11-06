From OSSVerify.reac_repacer.fuzz_uci Require Statements.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib Require Theorems.

Theorem plain_halts_holds : OSSVerify.reac_repacer.fuzz_uci.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Theorems.reac_repacer_fuzz_uci_plain_halts. Qed.
