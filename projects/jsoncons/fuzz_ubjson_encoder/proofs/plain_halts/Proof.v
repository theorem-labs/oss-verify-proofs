From OSSVerify.jsoncons.fuzz_ubjson_encoder Require Statements.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Theorems.

Theorem plain_halts_holds : OSSVerify.jsoncons.fuzz_ubjson_encoder.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Theorems.halts_allowed_jsoncons_fuzz_ubjson_encoder_halts_plain. Qed.
