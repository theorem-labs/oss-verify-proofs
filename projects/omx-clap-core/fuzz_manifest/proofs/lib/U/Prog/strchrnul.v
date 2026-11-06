From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import strchrnul_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require R_strchr.

Theorem strchrnul_holds : strchrnul_contract.
Proof. exact R_strchr.strchrnul_spec. Qed.
