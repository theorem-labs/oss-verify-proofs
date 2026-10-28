From Stdlib Require Import QArith.
From OssFuzzTheorems.openssl.bignum Require Statements.
From OssFuzzTheorems.Proofs.openssl.bignum.lib Require ConstAccept.

Theorem asan_ubsan_disagrees_at_most_holds : OssFuzzTheorems.openssl.bignum.Statements.asan_ubsan_disagrees_at_most 0.
Proof. exact OssFuzzTheorems.Proofs.openssl.bignum.lib.ConstAccept.asan_ubsan_bound_0. Qed.
