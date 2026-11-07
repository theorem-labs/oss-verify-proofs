From OSSVerify.libtasn1.asn1_get_length_der_fuzzer Require Statements.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.B Require TopZZ.

Theorem ubsan_agrees_holds : OSSVerify.libtasn1.asn1_get_length_der_fuzzer.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.B.TopZZ.asn1_get_length_der_fuzzer_ubsan_equiv_shipped. Qed.
