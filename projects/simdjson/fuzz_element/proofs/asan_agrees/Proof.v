From OSSVerify.simdjson.fuzz_element Require Statements.
From OSSVerify.Proofs.simdjson.fuzz_element.lib Require Theorems.

Theorem asan_agrees_holds : OSSVerify.simdjson.fuzz_element.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.simdjson.fuzz_element.lib.Theorems.strong_universal_error_free_fuzz_element_asan. Qed.
