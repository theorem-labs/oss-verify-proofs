From Stdlib Require Import QArith.
From OssFuzzTheorems.jsoncons.fuzz_ubjson_parser_max Require Statements.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require ConstAccept.

Theorem asan_ubsan_disagrees_at_most_holds : OssFuzzTheorems.jsoncons.fuzz_ubjson_parser_max.Statements.asan_ubsan_disagrees_at_most 0.
Proof. exact OssFuzzTheorems.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ConstAccept.asan_ubsan_bound_0. Qed.
