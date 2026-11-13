From Stdlib Require Import QArith.
From OSSVerify.double_conversion.string_to_double_fuzzer Require Statements.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require BaseAsan.

Theorem asan_disagrees_at_most_holds : OSSVerify.double_conversion.string_to_double_fuzzer.Statements.asan_disagrees_at_most 0.
Proof. exact OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.BaseAsan.asan_bound_0. Qed.
