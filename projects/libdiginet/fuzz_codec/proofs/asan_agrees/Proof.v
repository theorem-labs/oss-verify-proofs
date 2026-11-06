From OSSVerify.libdiginet.fuzz_codec Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require AD2o.

Theorem asan_agrees_holds : OSSVerify.libdiginet.fuzz_codec.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.AD2o.codec_asan_agrees_closed. Qed.
