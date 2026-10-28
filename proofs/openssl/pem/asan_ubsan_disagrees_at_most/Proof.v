From Stdlib Require Import QArith.
From OssFuzzTheorems.openssl.pem Require Statements.
From OssFuzzTheorems.Proofs.openssl.pem.lib Require ConstAccept.

Theorem asan_ubsan_disagrees_at_most_holds : OssFuzzTheorems.openssl.pem.Statements.asan_ubsan_disagrees_at_most 0.
Proof. exact OssFuzzTheorems.Proofs.openssl.pem.lib.ConstAccept.asan_ubsan_bound_0. Qed.
