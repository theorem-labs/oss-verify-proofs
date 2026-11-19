From OSSVerify.jsoncons.fuzz_msgpack_encoder Require Statements.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Halts Require HaltsTops.

Theorem plain_halts_holds : OSSVerify.jsoncons.fuzz_msgpack_encoder.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Halts.HaltsTops.halts_jsoncons_fuzz_msgpack_encoder_plain. Qed.
