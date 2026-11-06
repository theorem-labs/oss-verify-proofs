From OSSVerify.libreac.fuzz_scene Require Statements.
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require AgreeScene.

Theorem ubsan_agrees_holds : OSSVerify.libreac.fuzz_scene.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.libreac.fuzz_scene.lib.AgreeScene.ubsan_agrees_holds. Qed.
