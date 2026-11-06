From OSSVerify.openssl.punycode Require Statements.
From OSSVerify.Proofs.openssl.punycode.lib Require ConstAccept.

Theorem ubsan_agreement_decidable_holds : OSSVerify.openssl.punycode.Statements.ubsan_agreement_decidable.
Proof. exact OSSVerify.Proofs.openssl.punycode.lib.ConstAccept.ubsan_decidable. Qed.
