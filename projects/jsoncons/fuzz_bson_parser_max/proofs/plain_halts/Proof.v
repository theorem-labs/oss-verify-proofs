From OSSVerify.jsoncons.fuzz_bson_parser_max Require Statements.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Theorems.

Theorem plain_halts_holds : OSSVerify.jsoncons.fuzz_bson_parser_max.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.Theorems.halts_allowed_jsoncons_fuzz_bson_parser_max_halts_plain. Qed.
