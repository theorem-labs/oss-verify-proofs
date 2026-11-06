From OSSVerify.reac_pw.fuzz_segconf Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Theorems.

Theorem ubsan_halts_holds : OSSVerify.reac_pw.fuzz_segconf.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Theorems.reac_pw_fuzz_segconf_ubsan_halts. Qed.
