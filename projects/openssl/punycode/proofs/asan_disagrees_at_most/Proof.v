From Stdlib Require Import QArith.
From OSSVerify.openssl.punycode Require Statements.
From OSSVerify.Proofs.openssl.punycode.lib Require ConstAccept.

Theorem asan_disagrees_at_most_holds : OSSVerify.openssl.punycode.Statements.asan_disagrees_at_most 0.
Proof. exact OSSVerify.Proofs.openssl.punycode.lib.ConstAccept.asan_bound_0. Qed.
