From OSSVerify.reac_pw.fuzz_headamp Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require AD2o.

Theorem asan_agrees_holds : OSSVerify.reac_pw.fuzz_headamp.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.AD2o.headamp_asan_agrees_closed. Qed.
