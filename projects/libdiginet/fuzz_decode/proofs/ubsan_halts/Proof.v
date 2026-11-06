From OSSVerify.libdiginet.fuzz_decode Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Theorems.

Theorem ubsan_halts_holds : OSSVerify.libdiginet.fuzz_decode.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Theorems.libdiginet_fuzz_decode_ubsan_halts. Qed.
