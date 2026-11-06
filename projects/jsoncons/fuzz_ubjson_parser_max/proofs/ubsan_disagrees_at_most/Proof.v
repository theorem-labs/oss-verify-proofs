From Stdlib Require Import QArith.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max Require Statements.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require ConstAccept.

Theorem ubsan_disagrees_at_most_holds : OSSVerify.jsoncons.fuzz_ubjson_parser_max.Statements.ubsan_disagrees_at_most 0.
Proof. exact OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ConstAccept.ubsan_bound_0. Qed.
