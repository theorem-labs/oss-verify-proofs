From OSSVerify.leptonica.fhmtgen_fuzzer Require Statements.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.leptonica.fhmtgen_fuzzer.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Theorems.fhmtgen_fuzzer_ubsan_agrees. Qed.
