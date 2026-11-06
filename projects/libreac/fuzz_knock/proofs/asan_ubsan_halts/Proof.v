From OSSVerify.libreac.fuzz_knock Require Statements.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require YD2o.

Theorem asan_ubsan_halts_holds : OSSVerify.libreac.fuzz_knock.Statements.asan_ubsan_halts.
Proof. exact OSSVerify.Proofs.libreac.fuzz_knock.lib.AU.YD2o.knock_asan_ubsan_halts_closed. Qed.
