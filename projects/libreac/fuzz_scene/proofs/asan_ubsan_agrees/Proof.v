From OSSVerify.libreac.fuzz_scene Require Statements.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require G_Close.

Theorem asan_ubsan_agrees_holds : OSSVerify.libreac.fuzz_scene.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.G_Close.scene_asan_ubsan_agrees_of_rows. Qed.
