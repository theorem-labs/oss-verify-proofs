From OSSVerify.libreac.fuzz_scene Require Statements.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require G_Close.

Theorem asan_agrees_holds : OSSVerify.libreac.fuzz_scene.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.libreac.fuzz_scene.lib.A.G_Close.scene_asan_agrees_of_rows. Qed.
