From Stdlib Require Import QArith.
From OSSVerify.openssl.bndiv Require Statements.
From OSSVerify.Proofs.openssl.bndiv.lib Require ConstAccept.

Theorem asan_disagrees_at_most_holds : OSSVerify.openssl.bndiv.Statements.asan_disagrees_at_most 0.
Proof. exact OSSVerify.Proofs.openssl.bndiv.lib.ConstAccept.asan_bound_0. Qed.
