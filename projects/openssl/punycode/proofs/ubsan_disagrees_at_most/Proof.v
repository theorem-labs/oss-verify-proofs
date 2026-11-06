From Stdlib Require Import QArith.
From OSSVerify.openssl.punycode Require Statements.
From OSSVerify.Proofs.openssl.punycode.lib Require ConstAccept.

Theorem ubsan_disagrees_at_most_holds : OSSVerify.openssl.punycode.Statements.ubsan_disagrees_at_most 0.
Proof. exact OSSVerify.Proofs.openssl.punycode.lib.ConstAccept.ubsan_bound_0. Qed.
