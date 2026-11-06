From OSSVerify.libreac.fuzz_identity Require Statements.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require IdentTop.

Theorem asan_agrees_holds : OSSVerify.libreac.fuzz_identity.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.libreac.fuzz_identity.lib.A.IdentTop.ident_asan_agrees_of_parts. Qed.
