From Stdlib Require Import QArith.
From OSSVerify.openssl.bignum Require Statements.
From OSSVerify.Proofs.openssl.bignum.lib Require ConstAccept.

Theorem asan_ubsan_disagrees_at_most_holds : OSSVerify.openssl.bignum.Statements.asan_ubsan_disagrees_at_most 0.
Proof. exact OSSVerify.Proofs.openssl.bignum.lib.ConstAccept.asan_ubsan_bound_0. Qed.
