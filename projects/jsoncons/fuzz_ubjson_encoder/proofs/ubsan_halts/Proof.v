From OSSVerify.jsoncons.fuzz_ubjson_encoder Require Statements.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Theorems.

Theorem ubsan_halts_holds : OSSVerify.jsoncons.fuzz_ubjson_encoder.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Theorems.halts_allowed_jsoncons_fuzz_ubjson_encoder_halts_ubsan. Qed.
