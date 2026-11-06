From OSSVerify.reac_pw.fuzz_role Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require YD2o.

Theorem asan_ubsan_agrees_holds : OSSVerify.reac_pw.fuzz_role.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU.YD2o.role_asan_ubsan_agrees_closed. Qed.
