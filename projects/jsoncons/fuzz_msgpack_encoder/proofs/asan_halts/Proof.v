From OSSVerify.jsoncons.fuzz_msgpack_encoder Require Statements.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Halts Require HaltsTops.

Theorem asan_halts_holds : OSSVerify.jsoncons.fuzz_msgpack_encoder.Statements.asan_halts.
Proof. exact OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Halts.HaltsTops.halts_jsoncons_fuzz_msgpack_encoder_asan. Qed.
