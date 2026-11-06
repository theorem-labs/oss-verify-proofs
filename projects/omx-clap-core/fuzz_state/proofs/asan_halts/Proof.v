From OSSVerify.omx_clap_core.fuzz_state Require Statements.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSClose.

Theorem asan_halts_holds : OSSVerify.omx_clap_core.fuzz_state.Statements.asan_halts.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSClose.fs_asan_halts_closed. Qed.
