From OSSVerify.omx_clap_core.fuzz_state Require Statements.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSCloseB.

Theorem asan_ubsan_agrees_holds : OSSVerify.omx_clap_core.fuzz_state.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSCloseB.fs_asan_ubsan_agrees_closed. Qed.
