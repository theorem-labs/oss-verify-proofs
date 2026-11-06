From OSSVerify.libreac.fuzz_identity Require Statements.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require IdentTop.

Theorem asan_halts_holds : OSSVerify.libreac.fuzz_identity.Statements.asan_halts.
Proof. exact OSSVerify.Proofs.libreac.fuzz_identity.lib.A.IdentTop.ident_asan_halts_of_parts. Qed.
