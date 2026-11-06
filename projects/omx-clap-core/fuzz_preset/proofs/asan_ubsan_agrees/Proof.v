From OSSVerify.omx_clap_core.fuzz_preset Require Statements.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetClosedTopsB.

Theorem asan_ubsan_agrees_holds : OSSVerify.omx_clap_core.fuzz_preset.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PresetClosedTopsB.preset_asan_ubsan_agrees_closed. Qed.
