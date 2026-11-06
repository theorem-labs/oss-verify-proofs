From OSSVerify.libreac.fuzz_decode Require Statements.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.libreac.fuzz_decode.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.libreac.fuzz_decode.lib.Theorems.libreac_fuzz_decode_ubsan_agrees. Qed.
