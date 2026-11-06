From OSSVerify.reac_pw.fuzz_link Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Theorems.

Theorem asan_agrees_holds : OSSVerify.reac_pw.fuzz_link.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_link.lib.Theorems.reac_pw_fuzz_link_asan_agrees. Qed.
