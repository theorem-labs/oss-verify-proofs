From OSSVerify.glaze.binary_reflection Require Statements.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.glaze.binary_reflection.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.glaze.binary_reflection.lib.Theorems.strong_universal_error_free_binary_reflection_ubsan. Qed.
