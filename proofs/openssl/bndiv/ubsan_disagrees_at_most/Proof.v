From Stdlib Require Import QArith.
From OssFuzzTheorems.openssl.bndiv Require Statements.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib Require ConstAccept.

Theorem ubsan_disagrees_at_most_holds : OssFuzzTheorems.openssl.bndiv.Statements.ubsan_disagrees_at_most 0.
Proof. exact OssFuzzTheorems.Proofs.openssl.bndiv.lib.ConstAccept.ubsan_bound_0. Qed.
