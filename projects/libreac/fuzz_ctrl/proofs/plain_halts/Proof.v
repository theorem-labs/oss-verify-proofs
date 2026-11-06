From OSSVerify.libreac.fuzz_ctrl Require Statements.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Segs.

Theorem plain_halts_holds : OSSVerify.libreac.fuzz_ctrl.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg.Segs.plain_halts_holds. Qed.
