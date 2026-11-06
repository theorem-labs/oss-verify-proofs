From OSSVerify.reac_pw.fuzz_rate Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require AD2o.

Theorem asan_agrees_holds : OSSVerify.reac_pw.fuzz_rate.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.AD2o.rate_asan_agrees_closed. Qed.
