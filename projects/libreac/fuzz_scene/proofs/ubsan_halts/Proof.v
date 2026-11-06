From OSSVerify.libreac.fuzz_scene Require Statements.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog.Seg Require SEntry.

Theorem ubsan_halts_holds : OSSVerify.libreac.fuzz_scene.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog.Seg.SEntry.ubsan_halts_holds. Qed.
