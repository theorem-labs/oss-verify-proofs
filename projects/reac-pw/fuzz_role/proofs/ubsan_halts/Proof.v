From OSSVerify.reac_pw.fuzz_role Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require Theorems.

Theorem ubsan_halts_holds : OSSVerify.reac_pw.fuzz_role.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_role.lib.Theorems.reac_pw_fuzz_role_ubsan_halts. Qed.
