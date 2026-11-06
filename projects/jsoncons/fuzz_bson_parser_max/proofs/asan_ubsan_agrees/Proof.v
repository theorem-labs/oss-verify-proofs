From OSSVerify.jsoncons.fuzz_bson_parser_max Require Statements.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OSSVerify.jsoncons.fuzz_bson_parser_max.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.Theorems.strong_universal_error_free_fuzz_bson_parser_max_both. Qed.
