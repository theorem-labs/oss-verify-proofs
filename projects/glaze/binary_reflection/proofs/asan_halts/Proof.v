From OSSVerify.glaze.binary_reflection Require Statements.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require HaltsStmts.

Theorem asan_halts_holds : OSSVerify.glaze.binary_reflection.Statements.asan_halts.
Proof. exact OSSVerify.Proofs.glaze.binary_reflection.lib.HaltsStmts.asan_halts. Qed.
