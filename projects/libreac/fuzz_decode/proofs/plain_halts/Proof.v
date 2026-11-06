From OSSVerify.libreac.fuzz_decode Require Statements.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Theorems.

Theorem plain_halts_holds : OSSVerify.libreac.fuzz_decode.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.libreac.fuzz_decode.lib.Theorems.libreac_fuzz_decode_plain_halts. Qed.
