From OSSVerify.libreac.fuzz_scene Require Statements.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog.Seg Require SEntry.

Theorem plain_halts_holds : OSSVerify.libreac.fuzz_scene.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog.Seg.SEntry.plain_halts_holds. Qed.
