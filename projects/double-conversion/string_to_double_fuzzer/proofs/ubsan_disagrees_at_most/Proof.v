From Stdlib Require Import QArith.
From OSSVerify.double_conversion.string_to_double_fuzzer Require Statements.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require ConstAccept.

Theorem ubsan_disagrees_at_most_holds : OSSVerify.double_conversion.string_to_double_fuzzer.Statements.ubsan_disagrees_at_most 0.
Proof. exact OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ConstAccept.ubsan_bound_0. Qed.
