From OSSVerify.libdiginet.fuzz_codec Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Theorems.

Theorem plain_halts_may_fail_holds : OSSVerify.libdiginet.fuzz_codec.Statements.plain_halts_may_fail.
Proof. exact OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Theorems.libdiginet_fuzz_codec_plain_halts_may_fail. Qed.
