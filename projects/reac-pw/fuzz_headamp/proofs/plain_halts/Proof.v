From OSSVerify.reac_pw.fuzz_headamp Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Theorems.

Theorem plain_halts_holds : OSSVerify.reac_pw.fuzz_headamp.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Theorems.reac_pw_fuzz_headamp_plain_halts. Qed.
