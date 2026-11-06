From OSSVerify.libreac.fuzz_knock Require Statements.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require AD2o.

Theorem asan_halts_holds : OSSVerify.libreac.fuzz_knock.Statements.asan_halts.
Proof. exact OSSVerify.Proofs.libreac.fuzz_knock.lib.A.AD2o.knock_asan_halts_closed. Qed.
