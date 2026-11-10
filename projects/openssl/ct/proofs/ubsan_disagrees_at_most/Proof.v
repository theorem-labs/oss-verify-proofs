From Stdlib Require Import QArith.
From OSSVerify.openssl.ct Require Statements.
From OSSVerify.Proofs.openssl.ct.lib Require ConstAccept.

Theorem ubsan_disagrees_at_most_holds : OSSVerify.openssl.ct.Statements.ubsan_disagrees_at_most 0.
Proof. exact OSSVerify.Proofs.openssl.ct.lib.ConstAccept.ubsan_bound_0. Qed.
