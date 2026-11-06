From OSSVerify.libreac.fuzz_scene Require Statements.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require G_Close.

Theorem asan_halts_holds : OSSVerify.libreac.fuzz_scene.Statements.asan_halts.
Proof. exact OSSVerify.Proofs.libreac.fuzz_scene.lib.A.G_Close.scene_asan_halts_of_rows. Qed.
