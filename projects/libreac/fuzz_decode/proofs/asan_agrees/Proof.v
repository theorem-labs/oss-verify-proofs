From OSSVerify.libreac.fuzz_decode Require Statements.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Theorems.

Theorem asan_agrees_holds : OSSVerify.libreac.fuzz_decode.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.libreac.fuzz_decode.lib.Theorems.libreac_fuzz_decode_asan_agrees. Qed.
