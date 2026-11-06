From OSSVerify.boost_json.fuzz_parse Require Statements.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Theorems.

Theorem asan_ubsan_halts_holds : OSSVerify.boost_json.fuzz_parse.Statements.asan_ubsan_halts.
Proof. exact OSSVerify.Proofs.boost_json.fuzz_parse.lib.Theorems.halts_allowed_boost_json_halts_both. Qed.
