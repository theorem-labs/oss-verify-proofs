From OSSVerify.reac_pw.fuzz_segconf Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.reac_pw.fuzz_segconf.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Theorems.reac_pw_fuzz_segconf_ubsan_agrees. Qed.
