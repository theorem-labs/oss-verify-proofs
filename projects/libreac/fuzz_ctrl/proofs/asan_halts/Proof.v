From OSSVerify.libreac.fuzz_ctrl Require Statements.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ACtlAsanFinal.

Theorem asan_halts_holds : OSSVerify.libreac.fuzz_ctrl.Statements.asan_halts.
Proof. exact OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlAsanFinal.ctrl_asan_halts_closed. Qed.
