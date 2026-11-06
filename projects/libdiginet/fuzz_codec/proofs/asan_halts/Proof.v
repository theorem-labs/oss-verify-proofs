From OSSVerify.libdiginet.fuzz_codec Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require AD2o.

Theorem asan_halts_holds : OSSVerify.libdiginet.fuzz_codec.Statements.asan_halts.
Proof. exact OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.AD2o.codec_asan_halts_closed. Qed.
