From Stdlib Require Import QArith.
From OSSVerify.fast_float.from_chars Require Statements.
From OSSVerify.Proofs.fast_float.from_chars.lib Require ConstAccept.

Theorem asan_disagrees_at_most_holds : OSSVerify.fast_float.from_chars.Statements.asan_disagrees_at_most 0.
Proof. exact OSSVerify.Proofs.fast_float.from_chars.lib.ConstAccept.asan_bound_0. Qed.
