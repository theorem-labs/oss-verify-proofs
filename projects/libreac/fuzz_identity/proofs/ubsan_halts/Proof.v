From OSSVerify.libreac.fuzz_identity Require Statements.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Theorems.

Theorem ubsan_halts_holds : OSSVerify.libreac.fuzz_identity.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.libreac.fuzz_identity.lib.Theorems.libreac_fuzz_identity_ubsan_halts. Qed.
