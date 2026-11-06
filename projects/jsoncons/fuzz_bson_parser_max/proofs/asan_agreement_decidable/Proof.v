From OSSVerify.jsoncons.fuzz_bson_parser_max Require Statements.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require ConstAccept.

Theorem asan_agreement_decidable_holds : OSSVerify.jsoncons.fuzz_bson_parser_max.Statements.asan_agreement_decidable.
Proof. exact OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.ConstAccept.asan_decidable. Qed.
