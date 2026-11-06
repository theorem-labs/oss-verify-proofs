From Stdlib Require Import QArith.
From OSSVerify.openssl.pem Require Statements.
From OSSVerify.Proofs.openssl.pem.lib Require ConstAccept.

Theorem asan_ubsan_disagrees_at_most_holds : OSSVerify.openssl.pem.Statements.asan_ubsan_disagrees_at_most 0.
Proof. exact OSSVerify.Proofs.openssl.pem.lib.ConstAccept.asan_ubsan_bound_0. Qed.
