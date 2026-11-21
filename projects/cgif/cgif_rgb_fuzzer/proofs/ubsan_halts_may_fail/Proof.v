From OSSVerify.cgif.cgif_rgb_fuzzer Require Statements.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require UbsanTops.

Theorem ubsan_halts_may_fail_holds : OSSVerify.cgif.cgif_rgb_fuzzer.Statements.ubsan_halts_may_fail.
Proof. exact OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib.UbsanTops.halts_ubs2. Qed.
