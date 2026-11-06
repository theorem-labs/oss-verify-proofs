From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import strlen_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require R_strlen.

Theorem strlen_holds : strlen_contract.
Proof. exact R_strlen.strlen_spec. Qed.
