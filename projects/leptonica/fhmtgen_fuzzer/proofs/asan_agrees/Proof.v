From OSSVerify.leptonica.fhmtgen_fuzzer Require Statements.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib Require Theorems.

Theorem asan_agrees_holds : OSSVerify.leptonica.fhmtgen_fuzzer.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Theorems.fhmtgen_fuzzer_asan_agrees. Qed.
