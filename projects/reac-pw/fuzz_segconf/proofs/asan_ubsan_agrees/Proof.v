From OSSVerify.reac_pw.fuzz_segconf Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require SegTopB.

Theorem asan_ubsan_agrees_holds : OSSVerify.reac_pw.fuzz_segconf.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.SegTopB.seg_asan_ubsan_agrees_of_parts. Qed.
