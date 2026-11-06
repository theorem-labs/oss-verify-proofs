From OSSVerify.omx_clap_core.fuzz_preset Require Statements.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Theorems.

Theorem plain_halts_holds : OSSVerify.omx_clap_core.fuzz_preset.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Theorems.omx_clap_core_fuzz_preset_plain_halts. Qed.
