From OSSVerify.libreac.fuzz_disco Require Statements.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Theorems.

Theorem asan_agrees_holds : OSSVerify.libreac.fuzz_disco.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.libreac.fuzz_disco.lib.Theorems.libreac_fuzz_disco_asan_agrees. Qed.
