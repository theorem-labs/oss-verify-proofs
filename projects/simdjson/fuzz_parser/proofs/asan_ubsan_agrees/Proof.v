From OSSVerify.simdjson.fuzz_parser Require Statements.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OSSVerify.simdjson.fuzz_parser.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.simdjson.fuzz_parser.lib.Theorems.fuzz_parser_both_cfg. Qed.
