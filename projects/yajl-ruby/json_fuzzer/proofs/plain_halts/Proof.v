From OSSVerify.yajl_ruby.json_fuzzer Require Statements.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib Require Theorems.

Theorem plain_halts_holds : OSSVerify.yajl_ruby.json_fuzzer.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Theorems.halts_allowed_yajl_ruby_json_fuzzer_halts_plain. Qed.
