From Stdlib Require Import QArith.
From OSSVerify.libtasn1.asn1_get_length_der_fuzzer Require Statements.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.B Require ConstAccept.

Theorem ubsan_disagrees_at_most_holds : OSSVerify.libtasn1.asn1_get_length_der_fuzzer.Statements.ubsan_disagrees_at_most 0.
Proof. exact OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.B.ConstAccept.ubsan_bound_0. Qed.
