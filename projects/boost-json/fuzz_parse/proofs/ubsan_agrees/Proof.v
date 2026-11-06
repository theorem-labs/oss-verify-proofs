From OSSVerify.boost_json.fuzz_parse Require Statements.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Theorems.

Theorem ubsan_agrees_holds : Statements.ubsan_agrees.
Proof. exact Theorems.strong_universal_error_free_boost_json_ubsan. Qed.
