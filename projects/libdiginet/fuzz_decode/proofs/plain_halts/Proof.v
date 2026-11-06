From OSSVerify.libdiginet.fuzz_decode Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Theorems.

Theorem plain_halts_holds : OSSVerify.libdiginet.fuzz_decode.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Theorems.libdiginet_fuzz_decode_plain_halts. Qed.
