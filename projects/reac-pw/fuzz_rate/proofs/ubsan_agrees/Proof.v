From OSSVerify.reac_pw.fuzz_rate Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.reac_pw.fuzz_rate.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Theorems.reac_pw_fuzz_rate_ubsan_agrees. Qed.
