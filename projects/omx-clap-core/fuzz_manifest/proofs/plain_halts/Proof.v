From OSSVerify.omx_clap_core.fuzz_manifest Require Statements.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Theorems.

Theorem plain_halts_holds : OSSVerify.omx_clap_core.fuzz_manifest.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Theorems.omx_clap_core_fuzz_manifest_plain_halts. Qed.
