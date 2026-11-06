From OSSVerify.reac_pw.fuzz_pin Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require AD2o.

Theorem asan_agrees_holds : OSSVerify.reac_pw.fuzz_pin.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AD2o.pin_asan_agrees_closed. Qed.
