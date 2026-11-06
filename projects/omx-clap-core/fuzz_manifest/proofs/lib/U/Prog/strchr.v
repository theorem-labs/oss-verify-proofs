From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import strchr_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require R_strchr.

Theorem strchr_holds : strchr_contract.
Proof. exact R_strchr.strchr_spec. Qed.
