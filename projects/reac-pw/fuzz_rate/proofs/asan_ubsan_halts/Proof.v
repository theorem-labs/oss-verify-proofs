From OSSVerify.reac_pw.fuzz_rate Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require YD2o.

Theorem asan_ubsan_halts_holds : OSSVerify.reac_pw.fuzz_rate.Statements.asan_ubsan_halts.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.YD2o.rate_asan_ubsan_halts_closed. Qed.
