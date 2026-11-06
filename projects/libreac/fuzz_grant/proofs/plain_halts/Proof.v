From OSSVerify.libreac.fuzz_grant Require Statements.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Theorems.

Theorem plain_halts_holds : OSSVerify.libreac.fuzz_grant.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.libreac.fuzz_grant.lib.Theorems.libreac_fuzz_grant_plain_halts. Qed.
