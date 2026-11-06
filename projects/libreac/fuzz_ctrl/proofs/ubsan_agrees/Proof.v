From OSSVerify.libreac.fuzz_ctrl Require Statements.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require CtrlAgree.

Theorem ubsan_agrees_holds : OSSVerify.libreac.fuzz_ctrl.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.libreac.fuzz_ctrl.lib.CtrlAgree.ubsan_agrees_holds. Qed.
