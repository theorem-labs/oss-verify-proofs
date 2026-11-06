From OSSVerify.libreac.fuzz_knock Require Statements.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require AD2o.

Theorem asan_agrees_holds : OSSVerify.libreac.fuzz_knock.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.libreac.fuzz_knock.lib.A.AD2o.knock_asan_agrees_closed. Qed.
