From OSSVerify.reac_pw.fuzz_headamp Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Theorems.

Theorem ubsan_halts_holds : OSSVerify.reac_pw.fuzz_headamp.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Theorems.reac_pw_fuzz_headamp_ubsan_halts. Qed.
