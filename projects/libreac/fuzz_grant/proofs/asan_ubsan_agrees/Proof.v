From OSSVerify.libreac.fuzz_grant Require Statements.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OSSVerify.libreac.fuzz_grant.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.libreac.fuzz_grant.lib.Theorems.libreac_fuzz_grant_asan_ubsan_agrees. Qed.
