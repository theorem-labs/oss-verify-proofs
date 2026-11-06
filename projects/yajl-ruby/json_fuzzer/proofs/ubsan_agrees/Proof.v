From OSSVerify.yajl_ruby.json_fuzzer Require Statements.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.yajl_ruby.json_fuzzer.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Theorems.strong_universal_error_free_json_fuzzer_ubsan. Qed.
