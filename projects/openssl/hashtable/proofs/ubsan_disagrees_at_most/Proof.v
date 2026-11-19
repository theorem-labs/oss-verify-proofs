From Stdlib Require Import QArith.
From OSSVerify.openssl.hashtable Require Statements.
From OSSVerify.Proofs.openssl.hashtable.lib Require ConstAccept.

Theorem ubsan_disagrees_at_most_holds : OSSVerify.openssl.hashtable.Statements.ubsan_disagrees_at_most 0.
Proof. exact OSSVerify.Proofs.openssl.hashtable.lib.ConstAccept.ubsan_bound_0. Qed.
