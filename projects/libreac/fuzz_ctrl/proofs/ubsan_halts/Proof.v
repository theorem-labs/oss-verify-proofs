From OSSVerify.libreac.fuzz_ctrl Require Statements.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Segs.

Theorem ubsan_halts_holds : OSSVerify.libreac.fuzz_ctrl.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg.Segs.ubsan_halts_holds. Qed.
