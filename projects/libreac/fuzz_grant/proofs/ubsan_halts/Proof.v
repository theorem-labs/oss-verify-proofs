From OSSVerify.libreac.fuzz_grant Require Statements.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Theorems.

Theorem ubsan_halts_holds : OSSVerify.libreac.fuzz_grant.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.libreac.fuzz_grant.lib.Theorems.libreac_fuzz_grant_ubsan_halts. Qed.
