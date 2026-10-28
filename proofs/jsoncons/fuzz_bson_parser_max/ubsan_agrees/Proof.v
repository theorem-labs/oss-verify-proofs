From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max Require Statements.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Theorems.

Theorem ubsan_agrees_holds : OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.Statements.ubsan_agrees.
Proof. exact OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.Theorems.strong_universal_error_free_fuzz_bson_parser_max_ubsan. Qed.
