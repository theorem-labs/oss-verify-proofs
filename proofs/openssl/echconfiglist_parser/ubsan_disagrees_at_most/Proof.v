From Stdlib Require Import QArith.
From OssFuzzTheorems.openssl.echconfiglist_parser Require Statements.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require ConstAccept.

Theorem ubsan_disagrees_at_most_holds : OssFuzzTheorems.openssl.echconfiglist_parser.Statements.ubsan_disagrees_at_most 0.
Proof. exact OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.ConstAccept.ubsan_bound_0. Qed.
