From OSSVerify.simdjson.fuzz_parser Require Statements.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.simdjson.fuzz_parser.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.simdjson.fuzz_parser.lib.Theorems.fuzz_parser_ubsan_cfg. Qed.
