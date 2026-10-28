From Stdlib Require Import QArith.
From OssFuzzTheorems.openssl.hashtable Require Statements.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require ConstAccept.

Theorem asan_disagrees_at_most_holds : OssFuzzTheorems.openssl.hashtable.Statements.asan_disagrees_at_most 0.
Proof. exact OssFuzzTheorems.Proofs.openssl.hashtable.lib.ConstAccept.asan_bound_0. Qed.
