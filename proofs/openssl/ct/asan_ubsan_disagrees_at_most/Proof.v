From Stdlib Require Import QArith.
From OssFuzzTheorems.openssl.ct Require Statements.
From OssFuzzTheorems.Proofs.openssl.ct.lib Require ConstAccept.

Theorem asan_ubsan_disagrees_at_most_holds : OssFuzzTheorems.openssl.ct.Statements.asan_ubsan_disagrees_at_most 0.
Proof. exact OssFuzzTheorems.Proofs.openssl.ct.lib.ConstAccept.asan_ubsan_bound_0. Qed.
