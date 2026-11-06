From OSSVerify.omx_clap_core.fuzz_preset Require Statements.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.omx_clap_core.fuzz_preset.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Theorems.omx_clap_core_fuzz_preset_ubsan_agrees. Qed.
