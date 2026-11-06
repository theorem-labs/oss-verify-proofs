From OSSVerify.jsoncons.fuzz_ubjson_encoder Require Statements.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Theorems.

Theorem asan_agrees_holds : OSSVerify.jsoncons.fuzz_ubjson_encoder.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Theorems.strong_universal_error_free_fuzz_ubjson_encoder_asan. Qed.
