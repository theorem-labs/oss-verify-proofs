From Stdlib Require Import QArith.
From OssFuzzTheorems.openssl.punycode Require Statements.
From OssFuzzTheorems.Proofs.openssl.punycode.lib Require ConstAccept.

Theorem asan_disagrees_at_most_holds : OssFuzzTheorems.openssl.punycode.Statements.asan_disagrees_at_most 0.
Proof. exact OssFuzzTheorems.Proofs.openssl.punycode.lib.ConstAccept.asan_bound_0. Qed.
