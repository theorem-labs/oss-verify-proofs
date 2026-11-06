From OSSVerify.omx_clap_core.fuzz_preset Require Statements.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetClosedTopsA.

Theorem asan_halts_holds : OSSVerify.omx_clap_core.fuzz_preset.Statements.asan_halts.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PresetClosedTopsA.preset_asan_halts_closed. Qed.
