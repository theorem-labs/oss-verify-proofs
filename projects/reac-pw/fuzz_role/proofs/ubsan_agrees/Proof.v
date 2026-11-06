From OSSVerify.reac_pw.fuzz_role Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.reac_pw.fuzz_role.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_role.lib.Theorems.reac_pw_fuzz_role_ubsan_agrees. Qed.
