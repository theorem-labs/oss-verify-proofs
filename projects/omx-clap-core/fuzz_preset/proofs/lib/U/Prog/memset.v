From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import memset_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require R_memset.

Theorem memset_holds : memset_contract.
Proof. exact R_memset.memset_spec. Qed.
