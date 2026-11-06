From OSSVerify.reac_pw.fuzz_rate Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Theorems.

Theorem ubsan_halts_holds : OSSVerify.reac_pw.fuzz_rate.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Theorems.reac_pw_fuzz_rate_ubsan_halts. Qed.
