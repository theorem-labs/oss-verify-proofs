From OSSVerify.libreac.fuzz_disco Require Statements.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Theorems.

Theorem ubsan_halts_holds : OSSVerify.libreac.fuzz_disco.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.libreac.fuzz_disco.lib.Theorems.libreac_fuzz_disco_ubsan_halts. Qed.
