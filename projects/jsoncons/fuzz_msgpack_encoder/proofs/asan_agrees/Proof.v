From OSSVerify.jsoncons.fuzz_msgpack_encoder Require Statements.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Theorems.

Theorem asan_agrees_holds : OSSVerify.jsoncons.fuzz_msgpack_encoder.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Theorems.strong_universal_error_free_fuzz_msgpack_encoder_asan. Qed.
