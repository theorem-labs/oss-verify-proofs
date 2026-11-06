From OSSVerify.libdiginet.fuzz_codec Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require YD2o.

Theorem asan_ubsan_halts_holds : OSSVerify.libdiginet.fuzz_codec.Statements.asan_ubsan_halts.
Proof. exact OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.YD2o.codec_asan_ubsan_halts_closed. Qed.
