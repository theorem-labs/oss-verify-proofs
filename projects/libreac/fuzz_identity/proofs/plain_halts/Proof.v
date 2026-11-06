From OSSVerify.libreac.fuzz_identity Require Statements.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Theorems.

Theorem plain_halts_holds : OSSVerify.libreac.fuzz_identity.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.libreac.fuzz_identity.lib.Theorems.libreac_fuzz_identity_plain_halts. Qed.
