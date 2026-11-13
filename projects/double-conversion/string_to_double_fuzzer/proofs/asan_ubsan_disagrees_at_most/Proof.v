From Stdlib Require Import QArith.
From OSSVerify.double_conversion.string_to_double_fuzzer Require Statements.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require BaseBoth.

Theorem asan_ubsan_disagrees_at_most_holds : OSSVerify.double_conversion.string_to_double_fuzzer.Statements.asan_ubsan_disagrees_at_most 0.
Proof. exact OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.BaseBoth.both_bound_0. Qed.
