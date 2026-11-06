From OSSVerify.reac_pw.fuzz_headamp Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require YD2o.

Theorem asan_ubsan_halts_holds : OSSVerify.reac_pw.fuzz_headamp.Statements.asan_ubsan_halts.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.YD2o.headamp_asan_ubsan_halts_closed. Qed.
