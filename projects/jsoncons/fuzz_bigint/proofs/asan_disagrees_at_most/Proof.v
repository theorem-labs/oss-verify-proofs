From Stdlib Require Import QArith.
From OSSVerify.jsoncons.fuzz_bigint Require Statements.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require ConstAccept.

Theorem asan_disagrees_at_most_holds : OSSVerify.jsoncons.fuzz_bigint.Statements.asan_disagrees_at_most 0.
Proof. exact OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.ConstAccept.asan_bound_0. Qed.
