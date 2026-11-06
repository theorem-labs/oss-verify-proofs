From OSSVerify.yajl_ruby.json_fuzzer Require Statements.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib Require Theorems.

Theorem asan_ubsan_halts_holds : OSSVerify.yajl_ruby.json_fuzzer.Statements.asan_ubsan_halts.
Proof. exact OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Theorems.halts_allowed_yajl_ruby_json_fuzzer_halts_both. Qed.
