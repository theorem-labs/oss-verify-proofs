From Stdlib Require Import QArith.
From OssFuzzTheorems.openssl.bndiv Require Statements.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib Require ConstAccept.

Theorem asan_disagrees_at_most_holds : OssFuzzTheorems.openssl.bndiv.Statements.asan_disagrees_at_most 0.
Proof. exact OssFuzzTheorems.Proofs.openssl.bndiv.lib.ConstAccept.asan_bound_0. Qed.
