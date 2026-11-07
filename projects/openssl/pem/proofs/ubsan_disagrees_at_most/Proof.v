From Stdlib Require Import QArith.
From OSSVerify.openssl.pem Require Statements.
From OSSVerify.Proofs.openssl.pem.lib Require ConstAccept.

Theorem ubsan_disagrees_at_most_holds : OSSVerify.openssl.pem.Statements.ubsan_disagrees_at_most 0.
Proof. exact OSSVerify.Proofs.openssl.pem.lib.ConstAccept.ubsan_bound_0. Qed.
