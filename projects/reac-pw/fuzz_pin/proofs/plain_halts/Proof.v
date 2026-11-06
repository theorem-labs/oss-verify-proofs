From OSSVerify.reac_pw.fuzz_pin Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib Require Theorems.

Theorem plain_halts_holds : OSSVerify.reac_pw.fuzz_pin.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Theorems.reac_pw_fuzz_pin_plain_halts. Qed.
