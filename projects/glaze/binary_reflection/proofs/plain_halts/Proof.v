From OSSVerify.glaze.binary_reflection Require Statements.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require HaltsStmts.

Theorem plain_halts_holds : OSSVerify.glaze.binary_reflection.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.glaze.binary_reflection.lib.HaltsStmts.plain_halts. Qed.
