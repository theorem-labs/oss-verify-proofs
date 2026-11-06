From OSSVerify.reac_pw.fuzz_pin Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.reac_pw.fuzz_pin.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Theorems.reac_pw_fuzz_pin_ubsan_agrees. Qed.
