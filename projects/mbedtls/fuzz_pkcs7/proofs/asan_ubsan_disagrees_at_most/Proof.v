From Stdlib Require Import QArith.
From OSSVerify.mbedtls.fuzz_pkcs7 Require Statements.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib Require ConstAccept.

Theorem asan_ubsan_disagrees_at_most_holds : OSSVerify.mbedtls.fuzz_pkcs7.Statements.asan_ubsan_disagrees_at_most 0.
Proof. exact OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ConstAccept.asan_ubsan_bound_0. Qed.
