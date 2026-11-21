From OSSVerify.cgif.cgif_rgb_fuzzer Require Statements.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require UbsanTops.

Theorem ubsan_halts_holds : OSSVerify.cgif.cgif_rgb_fuzzer.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib.UbsanTops.halts_ubsan_forced_only. Qed.
