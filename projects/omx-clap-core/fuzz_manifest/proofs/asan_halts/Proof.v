From OSSVerify.omx_clap_core.fuzz_manifest Require Statements.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require FMFinal.

Theorem asan_halts_holds : OSSVerify.omx_clap_core.fuzz_manifest.Statements.asan_halts.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.FMFinal.fm_asan_halts. Qed.
