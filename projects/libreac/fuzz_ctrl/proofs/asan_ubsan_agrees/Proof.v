From OSSVerify.libreac.fuzz_ctrl Require Statements.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ACtlFinalB.

Theorem asan_ubsan_agrees_holds : OSSVerify.libreac.fuzz_ctrl.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.ACtlFinalB.ctrl_asan_ubsan_agrees_closed. Qed.
