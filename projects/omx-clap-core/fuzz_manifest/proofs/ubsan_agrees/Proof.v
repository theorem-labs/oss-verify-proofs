From OSSVerify.omx_clap_core.fuzz_manifest Require Statements.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require AgreeFm.

Theorem ubsan_agrees_holds : OSSVerify.omx_clap_core.fuzz_manifest.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog.AgreeFm.ubsan_agrees_holds. Qed.
