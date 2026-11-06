From OSSVerify.libreac.fuzz_identity Require Statements.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B Require IdentTopB.

Theorem asan_ubsan_agrees_holds : OSSVerify.libreac.fuzz_identity.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.libreac.fuzz_identity.lib.B.IdentTopB.identb_asan_ubsan_agrees_of_parts. Qed.
