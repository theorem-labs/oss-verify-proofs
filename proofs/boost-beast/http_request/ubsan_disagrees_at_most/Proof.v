From Stdlib Require Import QArith.
From OssFuzzTheorems.boost_beast.http_request Require Statements.
From OssFuzzTheorems.Proofs.boost_beast.http_request.lib Require ConstAccept.

Theorem ubsan_disagrees_at_most_holds : OssFuzzTheorems.boost_beast.http_request.Statements.ubsan_disagrees_at_most 0.
Proof. exact OssFuzzTheorems.Proofs.boost_beast.http_request.lib.ConstAccept.ubsan_bound_0. Qed.
