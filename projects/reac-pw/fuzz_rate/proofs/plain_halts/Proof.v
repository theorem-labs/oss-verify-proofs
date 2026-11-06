From OSSVerify.reac_pw.fuzz_rate Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Theorems.

Theorem plain_halts_holds : OSSVerify.reac_pw.fuzz_rate.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Theorems.reac_pw_fuzz_rate_plain_halts. Qed.
