From Stdlib Require Import QArith.
From OSSVerify.boost_beast.http_request Require Statements.
From OSSVerify.Proofs.boost_beast.http_request.lib Require ConstAccept.

Theorem asan_disagrees_at_most_holds : OSSVerify.boost_beast.http_request.Statements.asan_disagrees_at_most 0.
Proof. exact OSSVerify.Proofs.boost_beast.http_request.lib.ConstAccept.asan_bound_0. Qed.
