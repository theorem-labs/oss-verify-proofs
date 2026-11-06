From OSSVerify.jsoncons.fuzz_json_encoder Require Statements.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.jsoncons.fuzz_json_encoder.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.Theorems.strong_universal_error_free_fuzz_json_encoder_ubsan. Qed.
