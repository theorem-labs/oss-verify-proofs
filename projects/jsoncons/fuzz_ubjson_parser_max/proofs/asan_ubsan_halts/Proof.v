From OSSVerify.jsoncons.fuzz_ubjson_parser_max Require Statements.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Theorems.

Theorem asan_ubsan_halts_holds : OSSVerify.jsoncons.fuzz_ubjson_parser_max.Statements.asan_ubsan_halts.
Proof. exact OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Theorems.halts_allowed_jsoncons_fuzz_ubjson_parser_max_halts_both. Qed.
