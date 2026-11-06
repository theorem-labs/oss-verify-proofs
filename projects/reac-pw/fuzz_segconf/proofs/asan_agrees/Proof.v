From OSSVerify.reac_pw.fuzz_segconf Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require SegClose.

Theorem asan_agrees_holds : OSSVerify.reac_pw.fuzz_segconf.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.SegClose.seg_asan_agrees_closed. Qed.
