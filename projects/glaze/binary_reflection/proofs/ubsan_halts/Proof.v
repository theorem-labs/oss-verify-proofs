From OSSVerify.glaze.binary_reflection Require Statements.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require HaltsStmts.

Theorem ubsan_halts_holds : OSSVerify.glaze.binary_reflection.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.glaze.binary_reflection.lib.HaltsStmts.ubsan_halts. Qed.
