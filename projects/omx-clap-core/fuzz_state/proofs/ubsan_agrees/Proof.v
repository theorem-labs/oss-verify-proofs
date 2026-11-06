From OSSVerify.omx_clap_core.fuzz_state Require Statements.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require AgreeState.

Theorem ubsan_agrees_holds : OSSVerify.omx_clap_core.fuzz_state.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.AgreeState.ubsan_agrees_holds. Qed.
