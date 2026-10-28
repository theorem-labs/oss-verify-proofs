From Stdlib Require Import QArith.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer Require Statements.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require ConstAccept.

Theorem asan_disagrees_at_most_holds : OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.Statements.asan_disagrees_at_most 0.
Proof. exact OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ConstAccept.asan_bound_0. Qed.
