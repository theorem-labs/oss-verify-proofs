From OSSVerify.leptonica.edge_fuzzer Require Statements.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.leptonica.edge_fuzzer.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Theorems.strong_universal_error_free_edge_fuzzer_ubsan. Qed.
