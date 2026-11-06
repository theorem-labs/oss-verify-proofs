From Stdlib Require Import QArith.
From OSSVerify.openssl.bndiv Require Statements.
From OSSVerify.Proofs.openssl.bndiv.lib Require ConstAccept.

Theorem ubsan_disagrees_at_most_holds : OSSVerify.openssl.bndiv.Statements.ubsan_disagrees_at_most 0.
Proof. exact OSSVerify.Proofs.openssl.bndiv.lib.ConstAccept.ubsan_bound_0. Qed.
