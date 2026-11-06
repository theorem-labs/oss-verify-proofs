From Stdlib Require Import QArith.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer Require Statements.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require ConstAccept.

Theorem asan_disagrees_at_most_holds : OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Statements.asan_disagrees_at_most 0.
Proof. exact OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ConstAccept.asan_bound_0. Qed.
