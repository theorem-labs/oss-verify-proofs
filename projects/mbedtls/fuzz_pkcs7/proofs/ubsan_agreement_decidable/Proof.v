From OSSVerify.mbedtls.fuzz_pkcs7 Require Statements.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib Require ConstAccept.

Theorem ubsan_agreement_decidable_holds : OSSVerify.mbedtls.fuzz_pkcs7.Statements.ubsan_agreement_decidable.
Proof. exact OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ConstAccept.ubsan_decidable. Qed.
