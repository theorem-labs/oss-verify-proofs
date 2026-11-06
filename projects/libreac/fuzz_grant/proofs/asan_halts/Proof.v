From OSSVerify.libreac.fuzz_grant Require Statements.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Theorems.

Theorem asan_halts_holds : OSSVerify.libreac.fuzz_grant.Statements.asan_halts.
Proof. exact OSSVerify.Proofs.libreac.fuzz_grant.lib.Theorems.libreac_fuzz_grant_asan_halts. Qed.
