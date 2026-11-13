From OSSVerify.cjson.cjson_read_fuzzer Require Statements.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Halts Require HaltsTops.

Theorem plain_halts_holds : OSSVerify.cjson.cjson_read_fuzzer.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Halts.HaltsTops.halts_cjson_read_fuzzer_plain. Qed.
