From OSSVerify.omx_clap_core.fuzz_manifest Require Statements.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require FMW_llvmf_app.

Theorem asan_ubsan_halts_holds : OSSVerify.omx_clap_core.fuzz_manifest.Statements.asan_ubsan_halts.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_llvmf_app.fm_asan_ubsan_halts_B. Qed.
