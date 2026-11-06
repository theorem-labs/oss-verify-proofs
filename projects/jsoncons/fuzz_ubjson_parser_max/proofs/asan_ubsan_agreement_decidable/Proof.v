From OSSVerify.jsoncons.fuzz_ubjson_parser_max Require Statements.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require ConstAccept.

Theorem asan_ubsan_agreement_decidable_holds : OSSVerify.jsoncons.fuzz_ubjson_parser_max.Statements.asan_ubsan_agreement_decidable.
Proof. exact OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ConstAccept.asan_ubsan_decidable. Qed.
