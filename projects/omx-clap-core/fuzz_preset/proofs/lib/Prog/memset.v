From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import memset_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require R_memset.

Theorem memset_holds : memset_contract.
Proof. exact R_memset.memset_spec. Qed.
