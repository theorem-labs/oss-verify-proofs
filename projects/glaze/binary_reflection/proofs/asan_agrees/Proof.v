From OSSVerify.glaze.binary_reflection Require Statements.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Theorems.

Theorem asan_agrees_holds : OSSVerify.glaze.binary_reflection.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.glaze.binary_reflection.lib.Theorems.strong_universal_error_free_binary_reflection_asan. Qed.
