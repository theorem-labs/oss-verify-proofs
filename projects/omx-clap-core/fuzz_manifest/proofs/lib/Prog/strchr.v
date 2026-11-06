From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import strchr_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require R_strchr.

Theorem strchr_holds : strchr_contract.
Proof. exact R_strchr.strchr_spec. Qed.
