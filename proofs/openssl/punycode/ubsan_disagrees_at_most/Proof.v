From Stdlib Require Import QArith.
From OssFuzzTheorems.openssl.punycode Require Statements.
From OssFuzzTheorems.Proofs.openssl.punycode.lib Require ConstAccept.

Theorem ubsan_disagrees_at_most_holds : OssFuzzTheorems.openssl.punycode.Statements.ubsan_disagrees_at_most 0.
Proof. exact OssFuzzTheorems.Proofs.openssl.punycode.lib.ConstAccept.ubsan_bound_0. Qed.
