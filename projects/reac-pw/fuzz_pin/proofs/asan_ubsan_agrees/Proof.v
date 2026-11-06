From OSSVerify.reac_pw.fuzz_pin Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require YD2o.

Theorem asan_ubsan_agrees_holds : OSSVerify.reac_pw.fuzz_pin.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.YD2o.pin_asan_ubsan_agrees_closed. Qed.
