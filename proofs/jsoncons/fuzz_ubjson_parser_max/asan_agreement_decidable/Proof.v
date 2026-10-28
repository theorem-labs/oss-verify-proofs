From OssFuzzTheorems.jsoncons.fuzz_ubjson_parser_max Require Statements.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require ConstAccept.

Theorem asan_agreement_decidable_holds : OssFuzzTheorems.jsoncons.fuzz_ubjson_parser_max.Statements.asan_agreement_decidable.
Proof. exact OssFuzzTheorems.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ConstAccept.asan_decidable. Qed.
