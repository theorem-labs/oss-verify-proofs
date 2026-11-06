From OSSVerify.cgif.cgif_rgb_fuzzer Require Statements.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Theorems.

Theorem plain_halts_may_fail_holds : OSSVerify.cgif.cgif_rgb_fuzzer.Statements.plain_halts_may_fail.
Proof. exact OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib.Theorems.halts_allowed_cgif_cgif_rgb_fuzzer_halts_plain. Qed.
