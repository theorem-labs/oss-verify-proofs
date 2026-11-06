From OSSVerify.libreac.fuzz_ctrl Require Statements.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ACtlAsanFinal.

Theorem asan_agrees_holds : OSSVerify.libreac.fuzz_ctrl.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlAsanFinal.ctrl_asan_agrees_closed. Qed.
