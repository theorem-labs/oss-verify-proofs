From OSSVerify.omx_clap_core.fuzz_state Require Statements.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Theorems.

Theorem plain_halts_holds : OSSVerify.omx_clap_core.fuzz_state.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Theorems.omx_clap_core_fuzz_state_plain_halts. Qed.
