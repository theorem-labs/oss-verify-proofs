From OSSVerify.yajl_ruby.json_fuzzer Require Statements.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib Require Theorems.

Theorem asan_agrees_holds : OSSVerify.yajl_ruby.json_fuzzer.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Theorems.strong_universal_error_free_json_fuzzer_asan. Qed.
