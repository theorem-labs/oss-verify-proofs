From Stdlib Require Import QArith.
From OSSVerify.openssl.echconfiglist_parser Require Statements.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require ConstAccept.

Theorem ubsan_disagrees_at_most_holds : OSSVerify.openssl.echconfiglist_parser.Statements.ubsan_disagrees_at_most 0.
Proof. exact OSSVerify.Proofs.openssl.echconfiglist_parser.lib.ConstAccept.ubsan_bound_0. Qed.
