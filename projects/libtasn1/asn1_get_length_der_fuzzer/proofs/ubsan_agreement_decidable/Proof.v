From OSSVerify.libtasn1.asn1_get_length_der_fuzzer Require Statements.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.B Require ConstAccept.

Theorem ubsan_agreement_decidable_holds : OSSVerify.libtasn1.asn1_get_length_der_fuzzer.Statements.ubsan_agreement_decidable.
Proof. exact OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.B.ConstAccept.ubsan_decidable. Qed.
