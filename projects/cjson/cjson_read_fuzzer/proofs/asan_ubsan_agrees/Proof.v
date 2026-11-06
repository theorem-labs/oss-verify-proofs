From OSSVerify.cjson.cjson_read_fuzzer Require Statements.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OSSVerify.cjson.cjson_read_fuzzer.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Theorems.strong_universal_error_free_cjson_read_fuzzer_both. Qed.
