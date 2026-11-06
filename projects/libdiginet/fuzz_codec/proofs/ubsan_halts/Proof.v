From OSSVerify.libdiginet.fuzz_codec Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Theorems.

Theorem ubsan_halts_holds : OSSVerify.libdiginet.fuzz_codec.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Theorems.libdiginet_fuzz_codec_ubsan_halts. Qed.
