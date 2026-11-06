From OSSVerify.simdjson.fuzz_ondemand Require Statements.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.simdjson.fuzz_ondemand.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Theorems.strong_universal_error_free_fuzz_ondemand_ubsan. Qed.
