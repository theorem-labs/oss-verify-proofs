From OssFuzzTheorems.jsoncons.fuzz_ubjson_parser_max Require Statements.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require ConstAccept.

Theorem ubsan_agreement_decidable_holds : OssFuzzTheorems.jsoncons.fuzz_ubjson_parser_max.Statements.ubsan_agreement_decidable.
Proof. exact OssFuzzTheorems.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ConstAccept.ubsan_decidable. Qed.
