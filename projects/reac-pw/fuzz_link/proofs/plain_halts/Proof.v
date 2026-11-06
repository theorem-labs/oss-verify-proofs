From OSSVerify.reac_pw.fuzz_link Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Theorems.

Theorem plain_halts_holds : OSSVerify.reac_pw.fuzz_link.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_link.lib.Theorems.reac_pw_fuzz_link_plain_halts. Qed.
