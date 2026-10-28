From OssFuzzTheorems.leptonica.fhmtgen_fuzzer Require Statements.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib Require Theorems.

Theorem ubsan_agrees_holds : OssFuzzTheorems.leptonica.fhmtgen_fuzzer.Statements.ubsan_agrees.
Proof. exact OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Theorems.fhmtgen_fuzzer_ubsan_agrees. Qed.
