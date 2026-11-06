From OSSVerify.reac_pw.fuzz_segconf Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require SegClose.

Theorem asan_halts_holds : OSSVerify.reac_pw.fuzz_segconf.Statements.asan_halts.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.SegClose.seg_asan_halts_closed. Qed.
