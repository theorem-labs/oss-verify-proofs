From Stdlib Require Import QArith.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7 Require Statements.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib Require ConstAccept.

Theorem asan_disagrees_at_most_holds : OssFuzzTheorems.mbedtls.fuzz_pkcs7.Statements.asan_disagrees_at_most 0.
Proof. exact OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ConstAccept.asan_bound_0. Qed.
