From OSSVerify.reac_pw.fuzz_role Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require AD2o.

Theorem asan_halts_holds : OSSVerify.reac_pw.fuzz_role.Statements.asan_halts.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_role.lib.A.AD2o.role_asan_halts_closed. Qed.
