From OSSVerify.cjson.cjson_read_fuzzer Require Statements.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Halts Require HaltsTops.

Theorem ubsan_halts_holds : OSSVerify.cjson.cjson_read_fuzzer.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Halts.HaltsTops.halts_cjson_read_fuzzer_ubsan. Qed.
