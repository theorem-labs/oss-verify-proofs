From OSSVerify.jsoncons.fuzz_ubjson_parser_max Require Statements.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Theorems.

Theorem ubsan_halts_holds : OSSVerify.jsoncons.fuzz_ubjson_parser_max.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Theorems.halts_allowed_jsoncons_fuzz_ubjson_parser_max_halts_ubsan. Qed.
