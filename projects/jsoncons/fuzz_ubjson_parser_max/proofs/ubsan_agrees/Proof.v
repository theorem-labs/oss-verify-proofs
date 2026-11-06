From OSSVerify.jsoncons.fuzz_ubjson_parser_max Require Statements.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.jsoncons.fuzz_ubjson_parser_max.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Theorems.strong_universal_error_free_fuzz_ubjson_parser_max_ubsan. Qed.
